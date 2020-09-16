package org.kohsuke.groovy.sandbox;

import org.codehaus.groovy.ast.*;
import org.codehaus.groovy.ast.expr.*;
import org.codehaus.groovy.ast.stmt.ExpressionStatement;
import org.codehaus.groovy.control.SourceUnit;
import org.codehaus.groovy.syntax.Token;
import org.codehaus.groovy.syntax.Types;
import org.kohsuke.groovy.sandbox.impl.Ops;
import org.kohsuke.groovy.sandbox.impl.SandboxedMethodClosure;

import java.util.*;

import static org.codehaus.groovy.ast.expr.ArgumentListExpression.EMPTY_ARGUMENTS;
import static org.codehaus.groovy.syntax.Types.ASSIGNMENT_OPERATOR;
import static org.codehaus.groovy.syntax.Types.ofType;

public class VisitorImpl extends ScopeTrackingClassCodeExpressionTransformer {

    private final SourceUnit sourceUnit;
    /**
     * Invocation/property access without the left-hand side expression (for example {@code foo()}
     * as opposed to {@code something.foo()} means {@code this.foo()} in Java, but this is not
     * so in Groovy.
     *
     * In Groovy, {@code foo()} inside a closure uses the closure object itself as the lhs value,
     * whereas {@code this} in closure refers to a nearest enclosing non-closure object.
     *
     * So we cannot always expand {@code foo()} to {@code this.foo()}.
     *
     * To keep track of when we can expand {@code foo()} to {@code this.foo()} and when we can't,
     * we maintain this flag as we visit the expression tree. This flag is set to true
     * while we are visiting the body of the closure (the part between { ... }), and switched
     * back to false as we visit inner classes.
     *
     * To correctly expand {@code foo()} in the closure requires an access to the closure object itself,
     * and unfortunately Groovy doesn't seem to have any reliable way to do this. The hack I came up
     * with is {@code asWritable().getOwner()}, but even that is subject to the method resolution rule.
     *
     */
    private boolean visitingClosureBody;

    /**
     * Current class we are traversing.
     */
    private ClassNode clazz;
    
    private final SandboxTransformer sandboxTransformer;

    VisitorImpl(SourceUnit sourceUnit, ClassNode clazz, SandboxTransformer sandboxTransformer) {
        this.sourceUnit = sourceUnit;
        this.clazz = clazz;
        this.sandboxTransformer = sandboxTransformer;
    }

    private <T> void pushInReverseOrder(List<T> source, Stack<T> sink) {
        ListIterator<T> i = source.listIterator(source.size());
        while (i.hasPrevious()) {
            sink.push(i.previous());
        }
    }

    @Override
    public void visitMethod(MethodNode node) {
        if (clazz == null) { // compatibility
            clazz = node.getDeclaringClass();
        }
        super.visitMethod(node);
    }

    @Override
    public Expression transform(Expression exp) {
        final Stack<PseudoFrame> stack = new Stack<>();
        stack.push(new SimulatedTransform(exp));

        PseudoFrame current = null;

        while (!stack.empty()) {
            current = stack.pop();
            current.evaluateAndRecordResult(stack);
        }

        return null != current ? current.getResult() : exp;
    }

    abstract static class PseudoFrame {

        private PseudoFrameResult fr;

        private final Throwable creation;

        private static final boolean RECORD_CREATION_STACKTRACE;
        private static final String PROP_NAME = "DEBUG_SANDBOX_STACK";

        static {
            boolean b = false;
            try {
                b = Boolean.parseBoolean(System.getProperty(PROP_NAME));
            } catch (Throwable t) {
                System.err.println("Unable to get system property " + PROP_NAME + ": " + t.getMessage());
                t.printStackTrace();
            }
            RECORD_CREATION_STACKTRACE = b;
        }

        public PseudoFrame() {
            if (RECORD_CREATION_STACKTRACE) {
                this.creation = new Throwable();
            } else {
                this.creation = null;
            }
        }

        protected abstract PseudoFrameResult internalEvaluate(Stack<PseudoFrame> stack);

        public void evaluateAndRecordResult(Stack<PseudoFrame> stack) {
            fr = internalEvaluate(stack);
        }

        public boolean isEvaluated() {
            return null != fr;
        }

        public Expression getResult() {
            if (null != fr && fr.isReady()) {
                return fr.getResult();
            }
            throw new IllegalStateException("Corrupted sandbox stack: FrameResolution=" + fr, creation);
        }
    }

    private class SimulatedMakeCheckedCall extends PseudoFrame
    {
        private final String name;
        private final Object[] params;

        public SimulatedMakeCheckedCall(String name, Object... params) {
            super();
            this.name = name;
            this.params = params;
        }

        @Override
        public PseudoFrameResult internalEvaluate(Stack<PseudoFrame> stack)
        {
            Expression[] processedParams = new Expression[params.length];

            for (int i = 0; i < params.length; i++)
            {
                Object p = params[i];

                if (p instanceof PseudoFrame)
                {
                    Expression e = ((PseudoFrame)p).getResult();
                    processedParams[i] = e;
                }
                else
                {
                    processedParams[i] = (Expression) params[i];
                }
            }

            return new ActualResult(makeCheckedCall(name, processedParams));
        }
    }

    private class SimulatedTransform extends PseudoFrame
    {
        private final Expression exp;

        public SimulatedTransform(Expression input) {
            super();
            this.exp = input;
        }

        @Override
        protected PseudoFrameResult internalEvaluate(Stack<PseudoFrame> stack) {
            if (exp instanceof ClosureExpression) {
                // ClosureExpression.transformExpression doesn't visit the code inside
                ClosureExpression ce = (ClosureExpression)exp;
                try (StackVariableSet scope = new StackVariableSet(VisitorImpl.this)) {
                    Parameter[] parameters = ce.getParameters();
                    if (parameters != null) {
                        // Explicitly defined parameters, i.e., ".findAll { i -> i == 'bar' }"
                        if (parameters.length > 0) {
                            for (Parameter p : parameters) {
                                declareVariable(p);
                            }
                        } else {
                            // Implicit parameter - i.e., ".findAll { it == 'bar' }"
                            declareVariable(new Parameter(ClassHelper.DYNAMIC_TYPE, "it"));
                        }
                    }
                    boolean old = visitingClosureBody;
                    visitingClosureBody = true;
                    try {
                        ce.getCode().visit(VisitorImpl.this);
                    } finally {
                        visitingClosureBody = old;
                    }
                }
            }

            if (exp instanceof MethodCallExpression && sandboxTransformer.isInterceptMethodCall()) {
                // lhs.foo(arg1,arg2) => checkedCall(lhs,"foo",arg1,arg2)
                // lhs+rhs => lhs.plus(rhs)
                // Integer.plus(Integer) => DefaultGroovyMethods.plus
                // lhs || rhs => lhs.or(rhs)
                MethodCallExpression call = (MethodCallExpression) exp;

                Stack<PseudoFrame> temporaryStack = new Stack<>();

                Object objExp;
                if (call.isImplicitThis() && visitingClosureBody && !isLocalVariableExpression(call.getObjectExpression()))
                    objExp = SandboxTransformer.CLOSURE_THIS;
                else {
                    SimulatedTransform st = new SimulatedTransform(call.getObjectExpression());
                    temporaryStack.push(st);
                    objExp = st;
                }

                Expression arg1 = call.getMethod();
                SimulatedTransformArgumentsCall arg2 = transformArgumentsWithStack(call.getArguments(), temporaryStack);

                if (call.getObjectExpression() instanceof VariableExpression && ((VariableExpression) call.getObjectExpression()).getName().equals("super")) {
                    if (clazz == null) {
                        throw new IllegalStateException("owning class not defined");
                    }
                    SimulatedMakeCheckedCall smcc = new SimulatedMakeCheckedCall(
                            "checkedSuperCall", new ClassExpression(clazz), objExp, arg1, arg2);
                    temporaryStack.push(smcc);
                } else {
                    SimulatedMakeCheckedCall smcc = new SimulatedMakeCheckedCall("checkedCall",
                            objExp,
                            boolExp(call.isSafe()),
                            boolExp(call.isSpreadSafe()),
                            arg1,
                            arg2);
                    temporaryStack.push(smcc);
                }
                pushInReverseOrder(temporaryStack, stack);
                return new DelegatedResult(temporaryStack.lastElement());
            }

            if (exp instanceof StaticMethodCallExpression && sandboxTransformer.isInterceptMethodCall()) {
            /*
                Groovy doesn't use StaticMethodCallExpression as much as it could in compilation.
                For example, "Math.max(1,2)" results in a regular MethodCallExpression.

                Static import handling uses StaticMethodCallExpression, and so are some
                ASTTransformations like ToString,EqualsAndHashCode, etc.
             */
                StaticMethodCallExpression call = (StaticMethodCallExpression) exp;
                Stack<PseudoFrame> framesInCallOrder = new Stack<>();
                PseudoFrame args = transformArgumentsWithStack(call.getArguments(), framesInCallOrder);
                SimulatedMakeCheckedCall smcc = new SimulatedMakeCheckedCall("checkedStaticCall",
                        new ClassExpression(call.getOwnerType()),
                        new ConstantExpression(call.getMethod()),
                        args);
                framesInCallOrder.push(smcc);
                pushInReverseOrder(framesInCallOrder, stack);
                return new DelegatedResult(framesInCallOrder.lastElement());
            }

            if (exp instanceof MethodPointerExpression && sandboxTransformer.isInterceptMethodCall()) {
                MethodPointerExpression mpe = (MethodPointerExpression) exp;
                return new ActualResult(new ConstructorCallExpression( // TODO
                        new ClassNode(SandboxedMethodClosure.class),
                        new ArgumentListExpression(mpe.getExpression(), mpe.getMethodName())
                ));
            }

            if (exp instanceof ConstructorCallExpression && sandboxTransformer.isInterceptConstructor()) {
                if (!((ConstructorCallExpression) exp).isSpecialCall()) {
                    // creating a new instance, like "new Foo(...)"
                    Stack<PseudoFrame> framesInCallOrder = new Stack<>();
                    PseudoFrame pf = transformArgumentsWithStack(((ConstructorCallExpression) exp).getArguments(), framesInCallOrder);
                    framesInCallOrder.push(new SimulatedMakeCheckedCall("checkedConstructor",
                            new ClassExpression(exp.getType()),
                            pf));
                    pushInReverseOrder(framesInCallOrder, stack);
                    return new DelegatedResult(framesInCallOrder.lastElement());
                } else {
                    // we can't really intercept constructor calling super(...) or this(...),
                    // since it has to be the first method call in a constructor.
                    // but see SECURITY-582 fix above
                }
            }

            if (exp instanceof AttributeExpression && sandboxTransformer.isInterceptAttribute()) {
                AttributeExpression ae = (AttributeExpression) exp;
                SimulatedTransform objExpr = new SimulatedTransform(ae.getObjectExpression());
                SimulatedTransform prop = new SimulatedTransform(ae.getProperty());
                SimulatedMakeCheckedCall smcc = new SimulatedMakeCheckedCall("checkedGetAttribute",
                        objExpr,
                        boolExp(ae.isSafe()),
                        boolExp(ae.isSpreadSafe()),
                        prop);
                stack.push(smcc);
                stack.push(prop);
                stack.push(objExpr);
                return new DelegatedResult(smcc);
            }

            if (exp instanceof PropertyExpression && sandboxTransformer.isInterceptProperty()) {
                PropertyExpression pe = (PropertyExpression) exp;
                SimulatedMakeCheckedCall smcc;
                if (pe.isImplicitThis() && visitingClosureBody && !isLocalVariableExpression(pe.getObjectExpression())) {
                    SimulatedTransform p = new SimulatedTransform(pe.getProperty());
                    smcc = new SimulatedMakeCheckedCall("checkedGetProperty",
                            SandboxTransformer.CLOSURE_THIS,
                            boolExp(pe.isSafe()),
                            boolExp(pe.isSpreadSafe()),
                            p);
                    stack.push(smcc);
                    stack.push(p);
                } else {
                    SimulatedTransform oe = new SimulatedTransform(pe.getObjectExpression());
                    SimulatedTransform p = new SimulatedTransform(pe.getProperty());
                    smcc = new SimulatedMakeCheckedCall("checkedGetProperty",
                            oe,
                            boolExp(pe.isSafe()),
                            boolExp(pe.isSpreadSafe()),
                            p);
                    stack.push(smcc);
                    stack.push(p);
                    stack.push(oe);
                }
                return new DelegatedResult(smcc);
            }

            if (exp instanceof VariableExpression && sandboxTransformer.isInterceptProperty()) {
                VariableExpression vexp = (VariableExpression) exp;
                if (isLocalVariable(vexp.getName()) || vexp.getName().equals("this") || vexp.getName().equals("super")) {
                    // We don't care what sandboxed code does to itself until it starts interacting with outside world
                    //return VisitorImpl.super.transform(exp);
                    return new ActualResult(VisitorImpl.super.transform(exp));
                } else {
                    // if the variable is not in-scope local variable, it gets treated as a property access with implicit this.
                    // see AsmClassGenerator.visitVariableExpression and processClassVariable.
                    PropertyExpression pexp = new PropertyExpression(VariableExpression.THIS_EXPRESSION, vexp.getName());
                    pexp.setImplicitThis(true);
                    withLoc(exp, pexp);
                    SimulatedTransform st = new SimulatedTransform(pexp);
                    stack.push(st);
                    return new DelegatedResult(st);
                }
            }

            if (exp instanceof DeclarationExpression) {
                handleDeclarations((DeclarationExpression) exp);
            }

            if (exp instanceof BinaryExpression) {
                BinaryExpression be = (BinaryExpression) exp;
                // this covers everything from a+b to a=b
                if (ofType(be.getOperation().getType(),ASSIGNMENT_OPERATOR)) {
                    // simple assignment like '=' as well as compound assignments like "+=","-=", etc.

                    // How we dispatch this depends on the type of left expression.
                    //
                    // What can be LHS?
                    // according to AsmClassGenerator, PropertyExpression, AttributeExpression, FieldExpression, VariableExpression

                    Expression lhs = be.getLeftExpression();
                    if (lhs instanceof VariableExpression) {
                        VariableExpression vexp = (VariableExpression) lhs;
                        if (isLocalVariable(vexp.getName()) || vexp.getName().equals("this") || vexp.getName().equals("super")) {
                            // We don't care what sandboxed code does to itself until it starts interacting with outside world
                            return new ActualResult(VisitorImpl.super.transform(exp));
                        } else {
                            // if the variable is not in-scope local variable, it gets treated as a property access with implicit this.
                            // see AsmClassGenerator.visitVariableExpression and processClassVariable.
                            PropertyExpression pexp = new PropertyExpression(VariableExpression.THIS_EXPRESSION, vexp.getName());
                            pexp.setImplicitThis(true);
                            pexp.setSourcePosition(vexp);

                            lhs = pexp;
                        }
                    } // no else here
                    if (lhs instanceof PropertyExpression) {
                        PropertyExpression pe = (PropertyExpression) lhs;
                        String name = null;
                        if (lhs instanceof AttributeExpression) {
                            if (sandboxTransformer.isInterceptAttribute())
                                name = "checkedSetAttribute";
                        } else {
                            Expression receiver = pe.getObjectExpression();
                            if (receiver instanceof VariableExpression && ((VariableExpression) receiver).getName().equals("this")) {
                                FieldNode field = clazz != null ? clazz.getField(pe.getPropertyAsString()) : null;
                                if (field != null) { // could also verify that it is final, but not necessary
                                    // cf. BinaryExpression.transformExpression; VisitorImpl.super.transform(exp) transforms the LHS to checkedGetProperty
                                    return new ActualResult(new BinaryExpression(lhs, be.getOperation(), transform(be.getRightExpression())));
                                } // else this is a property which we need to check
                            }
                            if (sandboxTransformer.isInterceptProperty())
                                name = "checkedSetProperty";
                        }
                        if (name==null) {
                            // not intercepting?
                            return new ActualResult(VisitorImpl.super.transform(exp));
                        }

                        Stack<PseudoFrame> framesInCallOrder = new Stack<>();
                        Object objExp = transformObjectExpressionWithStack(pe, framesInCallOrder);
                        SimulatedTransform rightTransform = new SimulatedTransform(be.getRightExpression());
                        framesInCallOrder.push(rightTransform);
                        SimulatedMakeCheckedCall smcc = new SimulatedMakeCheckedCall(name,
                                objExp,
                                pe.getProperty(),
                                boolExp(pe.isSafe()),
                                boolExp(pe.isSpreadSafe()),
                                intExp(be.getOperation().getType()),
                                rightTransform);
                        framesInCallOrder.push(smcc);
                        pushInReverseOrder(framesInCallOrder, stack);
                        return new DelegatedResult(framesInCallOrder.lastElement());
                    } else
                    if (lhs instanceof FieldExpression) {
                        // while javadoc of FieldExpression isn't very clear,
                        // AsmClassGenerator maps this to GETSTATIC/SETSTATIC/GETFIELD/SETFIELD access.
                        // not sure how we can intercept this, so skipping this for now
                        return new ActualResult(VisitorImpl.super.transform(exp));
                    } else
                    if (lhs instanceof BinaryExpression) {
                        BinaryExpression lbe = (BinaryExpression) lhs;
                        if (lbe.getOperation().getType()== Types.LEFT_SQUARE_BRACKET && sandboxTransformer.isInterceptArray()) {// expression of the form "x[y] = z"
                            SimulatedTransform lbeLeft = new SimulatedTransform(lbe.getLeftExpression());
                            SimulatedTransform lbeRight = new SimulatedTransform(lbe.getRightExpression());
                            SimulatedTransform beRight = new SimulatedTransform(be.getRightExpression());
                            SimulatedMakeCheckedCall smcc = new SimulatedMakeCheckedCall(
                                    "checkedSetArray",
                                    lbeLeft,
                                    lbeRight,
                                    intExp(be.getOperation().getType()),
                                    beRight);
                            stack.push(smcc);
                            stack.push(beRight);
                            stack.push(lbeRight);
                            stack.push(lbeLeft);
                            return new DelegatedResult(smcc);
                        }
                    } else
                        throw new AssertionError("Unexpected LHS of an assignment: " + lhs.getClass());
                }
                if (be.getOperation().getType()==Types.LEFT_SQUARE_BRACKET) {// array reference
                    if (sandboxTransformer.isInterceptArray()) {
                        SimulatedTransform left = new SimulatedTransform(be.getLeftExpression());
                        SimulatedTransform right = new SimulatedTransform(be.getRightExpression());
                        SimulatedMakeCheckedCall smcc = new SimulatedMakeCheckedCall(
                                "checkedGetArray",
                                left,
                                right);
                        stack.push(smcc);
                        stack.push(right);
                        stack.push(left);
                        return new DelegatedResult(smcc);
                    }

                } else
                if (be.getOperation().getType()==Types.KEYWORD_INSTANCEOF) {// instanceof operator
                    return new ActualResult(VisitorImpl.super.transform(exp));
                } else
                if (Ops.isLogicalOperator(be.getOperation().getType())) {
                    return new ActualResult(VisitorImpl.super.transform(exp));
                } else
                if (be.getOperation().getType()==Types.KEYWORD_IN) {// membership operator: JENKINS-28154
                    // This requires inverted operand order:
                    // "a in [...]" -> "[...].isCase(a)"
                    if (sandboxTransformer.isInterceptMethodCall()) {
                        SimulatedTransform left = new SimulatedTransform(be.getLeftExpression());
                        SimulatedTransform right = new SimulatedTransform(be.getRightExpression());
                        SimulatedMakeCheckedCall smcc = new SimulatedMakeCheckedCall(
                                "checkedCall",
                                right,
                                boolExp(false),
                                boolExp(false),
                                stringExp("isCase"),
                                left);
                        stack.push(smcc);
                        stack.push(left);
                        stack.push(right);
                        return new DelegatedResult(smcc);
                    }
                } else
                if (Ops.isRegexpComparisonOperator(be.getOperation().getType())) {
                    if (sandboxTransformer.isInterceptMethodCall())
                    {
                        SimulatedTransform left = new SimulatedTransform(be.getLeftExpression());
                        SimulatedTransform right = new SimulatedTransform(be.getRightExpression());
                        SimulatedMakeCheckedCall smcc = new SimulatedMakeCheckedCall(
                                "checkedStaticCall",
                                classExp(SandboxTransformer.ScriptBytecodeAdapterClass),
                                stringExp(Ops.binaryOperatorMethods(be.getOperation().getType())),
                                left,
                                right);
                        stack.push(smcc);
                        stack.push(right);
                        stack.push(left);
                        return new DelegatedResult(smcc);
                    }
                } else
                if (Ops.isComparisionOperator(be.getOperation().getType())) {
                    if (sandboxTransformer.isInterceptMethodCall()) {
                        SimulatedTransform left = new SimulatedTransform(be.getLeftExpression());
                        SimulatedTransform right = new SimulatedTransform(be.getRightExpression());
                        SimulatedMakeCheckedCall smcc = new SimulatedMakeCheckedCall(
                                "checkedComparison",
                                left,
                                intExp(be.getOperation().getType()),
                                right);
                        stack.push(smcc);
                        stack.push(right);
                        stack.push(left);
                        return new DelegatedResult(smcc);
                    }
                } else
                if (sandboxTransformer.isInterceptMethodCall()) {
                    // normally binary operators like a+b
//                    // TODO: check what other weird binary operators land here
                    SimulatedTransform left = new SimulatedTransform(be.getLeftExpression());
                    SimulatedTransform right = new SimulatedTransform(be.getRightExpression());
                    SimulatedMakeCheckedCall smcc = new SimulatedMakeCheckedCall(
                            "checkedBinaryOp",
                            left,
                            intExp(be.getOperation().getType()),
                            right);

                    stack.push(smcc);
                    stack.push(right);
                    stack.push(left);
                    return new DelegatedResult(smcc);
                }
            }

            if (exp instanceof PostfixExpression) {
                PostfixExpression pe = (PostfixExpression) exp;
                Stack<PseudoFrame> framesInCallOrder = new Stack<>();
                prefixPostfixExpWithStack(exp, pe.getExpression(), pe.getOperation(), "Postfix", framesInCallOrder);
                pushInReverseOrder(framesInCallOrder, stack);
                return new DelegatedResult(framesInCallOrder.lastElement());
            }
            if (exp instanceof PrefixExpression) {
                PrefixExpression pe = (PrefixExpression) exp;
                Stack<PseudoFrame> framesInCallOrder = new Stack<>();
                prefixPostfixExpWithStack(exp, pe.getExpression(), pe.getOperation(), "Prefix", framesInCallOrder);
                pushInReverseOrder(framesInCallOrder, stack);
                return new DelegatedResult(framesInCallOrder.lastElement());
            }

            if (exp instanceof CastExpression) {
                CastExpression ce = (CastExpression) exp;
                SimulatedTransform st = new SimulatedTransform(ce.getExpression());
                SimulatedMakeCheckedCall smcc = new SimulatedMakeCheckedCall(
                        "checkedCast",
                        classExp(exp.getType()),
                        st,
                        boolExp(ce.isIgnoringAutoboxing()),
                        boolExp(ce.isCoerce()),
                        boolExp(ce.isStrict()));
                stack.push(smcc);
                stack.push(st);
                return new DelegatedResult(smcc);
            }

            return new ActualResult(VisitorImpl.super.transform(exp));
        }
    }

    class SimulatedTransformArgumentsCall extends PseudoFrame {

        private final Expression expression;
        private final List<SimulatedTransform> sts;

        public SimulatedTransformArgumentsCall(Expression expression, List<SimulatedTransform> sts) {
            super();
            this.expression = expression;
            this.sts = sts;
        }

        @Override
        public PseudoFrameResult internalEvaluate(Stack<PseudoFrame> stack) {
            List<Expression> exprs = new ArrayList<>(sts.size());

            for (SimulatedTransform st : sts)
            {
                exprs.add(st.getResult());
            }

            return new ActualResult(withLoc(expression, new MethodCallExpression(new ListExpression(exprs),
                    "toArray", new ArgumentListExpression())));
        }
    }

    private interface PseudoFrameResult {
        Expression getResult();

        boolean isReady();
    }

    /**
     * A fully-computed result {@link Expression}
     *
     * @see DelegatedResult
     */
    private static class ActualResult implements PseudoFrameResult {

        private final Expression result;

        public ActualResult(Expression result) {
            this.result = result;
        }

        @Override
        public Expression getResult() {
            return result;
        }

        @Override
        public boolean isReady() {
            return true;
        }
    }

    /**
     * A lazily-computed result {@link Expression}
     *
     * {@link #getResult()} may only be called after evaluation of the delegate passed to this class's constructor
     *
     * @see ActualResult
     */
    private static class DelegatedResult implements PseudoFrameResult {
        private final PseudoFrame delegate;

        public DelegatedResult(PseudoFrame delegate) {
            this.delegate = delegate;
        }

        @Override
        public Expression getResult() {
            return delegate.getResult();
        }

        @Override public boolean isReady() {
            return delegate.isEvaluated();
        }
    }

    /**
     * Transforms the arguments of a call.
     * Groovy primarily uses {@link ArgumentListExpression} for this,
     * but the signature doesn't guarantee that. So this method takes care of that.
     */
    SimulatedTransformArgumentsCall transformArgumentsWithStack(Expression e, Stack<PseudoFrame> framesInCallOrder) {

        SimulatedTransformArgumentsCall wc;

        if (e instanceof TupleExpression) {
            List<Expression> expressions = ((TupleExpression) e).getExpressions();
            ArrayList<SimulatedTransform> xfs = new ArrayList<>(expressions.size());
            for (Expression expression : expressions) {
                SimulatedTransform st = new SimulatedTransform(expression);
                xfs.add(st);
                framesInCallOrder.add(st);
            }
            wc = new SimulatedTransformArgumentsCall(e, xfs);
            framesInCallOrder.add(wc);
        } else {
            SimulatedTransform st = new SimulatedTransform(e);
            wc = new SimulatedTransformArgumentsCall(e, Collections.singletonList(st));
            framesInCallOrder.push(st);
            framesInCallOrder.push(wc);
        }

        return wc;
    }

    /**
     * Transforms the arguments of a call.
     * Groovy primarily uses {@link ArgumentListExpression} for this,
     * but the signature doesn't guarantee that. So this method takes care of that.
     */
    Expression transformArguments(Expression e) {
        List<Expression> l;
        if (e instanceof TupleExpression) {
            List<Expression> expressions = ((TupleExpression) e).getExpressions();
            l = new ArrayList<>(expressions.size());
            for (Expression expression : expressions) {
                l.add(transform(expression));
            }
        } else {
            l = Collections.singletonList(transform(e));
        }

        // checkedCall expects an array
        return withLoc(e,new MethodCallExpression(new ListExpression(l),"toArray",new ArgumentListExpression()));
    }

    Expression makeCheckedCall(String name, Expression... arguments) {
        return new StaticMethodCallExpression(sandboxTransformer.getCheckerClass(),name,
                new ArgumentListExpression(arguments));
    }

    private Object prefixPostfixExpWithStack(Expression whole, Expression atom, Token opToken, String mode, Stack<PseudoFrame> framesInCallOrder) {
        String op = opToken.getText().equals("++") ? "next" : "previous";

        // a[b]++
        if (atom instanceof BinaryExpression && ((BinaryExpression) atom).getOperation().getType()==Types.LEFT_SQUARE_BRACKET && sandboxTransformer.isInterceptArray()) {
            SimulatedTransform left = new SimulatedTransform(((BinaryExpression) atom).getLeftExpression());
            SimulatedTransform right = new SimulatedTransform(((BinaryExpression) atom).getRightExpression());
            SimulatedMakeCheckedCall smcc = new SimulatedMakeCheckedCall("checked" + mode + "Array",
                    left,
                    right,
                    stringExp(op));
            framesInCallOrder.push(left);
            framesInCallOrder.push(right);
            framesInCallOrder.push(smcc);
            return smcc;
        }

        // a++
        if (atom instanceof VariableExpression) {
            VariableExpression ve = (VariableExpression) atom;
            if (isLocalVariable(ve.getName())) {
                if (mode.equals("Postfix")) {
                    // a trick to rewrite a++ without introducing a new local variable
                    //     a++ -> [a,a=a.next()][0]
                    Expression e = withLoc(whole,new BinaryExpression(
                            new ListExpression(Arrays.asList(
                                    atom,
                                    new BinaryExpression(atom, SandboxTransformer.ASSIGNMENT_OP,
                                            withLoc(atom,new MethodCallExpression(atom,op,EMPTY_ARGUMENTS)))
                            )),
                            new Token(Types.LEFT_SQUARE_BRACKET, "[", -1,-1),
                            new ConstantExpression(0)
                    ));
                    SimulatedTransform st = new SimulatedTransform(e);
                    framesInCallOrder.push(st);
                    return st;
                } else {
                    // ++a -> a=a.next()
                    Expression e = withLoc(whole,new BinaryExpression(atom,SandboxTransformer.ASSIGNMENT_OP,
                            withLoc(atom,new MethodCallExpression(atom,op,EMPTY_ARGUMENTS)))
                    );
                    SimulatedTransform st = new SimulatedTransform(e);
                    framesInCallOrder.push(st);
                    return st;
                }
            } else {
                // if the variable is not in-scope local variable, it gets treated as a property access with implicit this.
                // see AsmClassGenerator.visitVariableExpression and processClassVariable.
                PropertyExpression pexp = new PropertyExpression(VariableExpression.THIS_EXPRESSION, ve.getName());
                pexp.setImplicitThis(true);
                pexp.setSourcePosition(atom);

                atom = pexp;
                // fall through to the "a.b++" case below
            }
        }

        // a.b++
        if (atom instanceof PropertyExpression && sandboxTransformer.isInterceptProperty()) {
            PropertyExpression pe = (PropertyExpression) atom;
            Object oe = transformObjectExpressionWithStack(pe, framesInCallOrder);
            SimulatedMakeCheckedCall smcc = new SimulatedMakeCheckedCall("checked" + mode + "Property",
                    oe,
                    pe.getProperty(),
                    boolExp(pe.isSafe()),
                    boolExp(pe.isSpreadSafe()),
                    stringExp(op));
            framesInCallOrder.push(smcc);
            return smcc;
        }

        return whole;
    }

    /**
     * Decorates an {@link ASTNode} by copying source location from another node.
     */
    private <T extends ASTNode> T withLoc(ASTNode src, T t) {
        t.setSourcePosition(src);
        return t;
    }

    /**
     * See {@link #visitingClosureBody} for the details of what this method is about.
     */
    private Object transformObjectExpressionWithStack(PropertyExpression exp, Stack<PseudoFrame> temporaryStack) {
        if (exp.isImplicitThis() && visitingClosureBody && !isLocalVariableExpression(exp.getObjectExpression())) {
            return SandboxTransformer.CLOSURE_THIS;
        } else {
//            return transform(exp.getObjectExpression());
            SimulatedTransform st = new SimulatedTransform(exp.getObjectExpression());
            temporaryStack.push(st);
            return st;
        }
    }

    private boolean isLocalVariableExpression(Expression exp) {
        if (exp != null && exp instanceof VariableExpression) {
            return isLocalVariable(((VariableExpression) exp).getName());
        }

        return false;
    }

    ConstantExpression boolExp(boolean v) {
        return v ? ConstantExpression.PRIM_TRUE : ConstantExpression.PRIM_FALSE;
    }

    ConstantExpression intExp(int v) {
        return new ConstantExpression(v,true);
    }

    ClassExpression classExp(ClassNode c) {
        return new ClassExpression(c);
    }

    ConstantExpression stringExp(String v) {
        return new ConstantExpression(v);
    }

    @Override
    public void visitExpressionStatement(ExpressionStatement es) {
        Expression exp = es.getExpression();
        if (exp instanceof DeclarationExpression) {
            DeclarationExpression de = (DeclarationExpression) exp;
            Expression leftExpression = de.getLeftExpression();
            if (leftExpression instanceof VariableExpression) {
                // Only cast and transform if the RHS is *not* an EmptyExpression, i.e., "String foo;" would not be cast/transformed.
                if (!(de.getRightExpression() instanceof EmptyExpression) &&
                        SandboxTransformer.mightBePositionalArgumentConstructor((VariableExpression) leftExpression)) { // TODO check this static call
                    CastExpression ce = new CastExpression(leftExpression.getType(), de.getRightExpression());
                    ce.setCoerce(true);
                    es.setExpression(transform(new DeclarationExpression(leftExpression, de.getOperation(), ce)));
                    return;
                }
            } else {
                throw new UnsupportedOperationException("not supporting tuples yet"); // cf. "Unexpected LHS of an assignment" above
            }
        }
        super.visitExpressionStatement(es);
    }

    @Override
    protected SourceUnit getSourceUnit() {
        return sourceUnit;
    }
}

