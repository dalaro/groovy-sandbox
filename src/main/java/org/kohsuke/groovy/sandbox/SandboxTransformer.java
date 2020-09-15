package org.kohsuke.groovy.sandbox;

import groovy.lang.Script;
import java.lang.reflect.Modifier;
import java.util.*;
import java.util.concurrent.atomic.AtomicReference;
import org.codehaus.groovy.GroovyBugError;
import org.codehaus.groovy.ast.ASTNode;
import org.codehaus.groovy.ast.ClassCodeExpressionTransformer;
import org.codehaus.groovy.ast.ClassHelper;
import org.codehaus.groovy.ast.ClassNode;
import org.codehaus.groovy.ast.ConstructorNode;
import org.codehaus.groovy.ast.FieldNode;
import org.codehaus.groovy.ast.MethodNode;
import org.codehaus.groovy.ast.Parameter;
import org.codehaus.groovy.ast.expr.ArgumentListExpression;
import org.codehaus.groovy.ast.expr.AttributeExpression;
import org.codehaus.groovy.ast.expr.CastExpression;
import org.codehaus.groovy.ast.expr.ClassExpression;
import org.codehaus.groovy.ast.expr.ClosureExpression;
import org.codehaus.groovy.ast.expr.ConstantExpression;
import org.codehaus.groovy.ast.expr.DeclarationExpression;
import org.codehaus.groovy.ast.expr.EmptyExpression;
import org.codehaus.groovy.ast.expr.Expression;
import org.codehaus.groovy.ast.expr.ListExpression;
import org.codehaus.groovy.ast.expr.MethodCallExpression;
import org.codehaus.groovy.ast.expr.MethodPointerExpression;
import org.codehaus.groovy.ast.expr.PostfixExpression;
import org.codehaus.groovy.ast.expr.PrefixExpression;
import org.codehaus.groovy.ast.expr.PropertyExpression;
import org.codehaus.groovy.ast.expr.StaticMethodCallExpression;
import org.codehaus.groovy.ast.expr.TupleExpression;
import org.codehaus.groovy.classgen.GeneratorContext;
import org.codehaus.groovy.control.CompilePhase;
import org.codehaus.groovy.control.SourceUnit;
import org.codehaus.groovy.control.customizers.CompilationCustomizer;
import org.codehaus.groovy.ast.expr.ConstructorCallExpression;
import org.codehaus.groovy.ast.expr.BinaryExpression;
import org.codehaus.groovy.runtime.ScriptBytecodeAdapter;
import org.codehaus.groovy.syntax.Token;
import org.codehaus.groovy.syntax.Types;
import org.codehaus.groovy.ast.expr.FieldExpression;
import org.codehaus.groovy.ast.expr.VariableExpression;
import org.kohsuke.groovy.sandbox.impl.Checker;
import org.kohsuke.groovy.sandbox.impl.Ops;
import org.kohsuke.groovy.sandbox.impl.SandboxedMethodClosure;

import static org.codehaus.groovy.ast.expr.ArgumentListExpression.EMPTY_ARGUMENTS;
import org.codehaus.groovy.ast.stmt.BlockStatement;
import org.codehaus.groovy.ast.stmt.ExpressionStatement;
import org.codehaus.groovy.ast.stmt.Statement;
import org.codehaus.groovy.runtime.typehandling.DefaultTypeTransformation;

import static org.codehaus.groovy.syntax.Types.*;

/**
 * Transforms Groovy code at compile-time to intercept when the script interacts with the outside world.
 *
 * <p>
 * Sometimes you'd like to run Groovy scripts in a sandbox environment, where you only want it to
 * access limited subset of the rest of JVM. This transformation makes that possible by letting you inspect
 * every step of the script execution when it makes method calls and property/field/array access.
 *
 * <p>
 * Once the script is transformed, every intercepted operation results in a call to {@link Checker},
 * which further forwards the call to {@link GroovyInterceptor} for inspection.
 *
 *
 * <p>
 * To use it, add it to the {@link org.codehaus.groovy.control.CompilerConfiguration}, like this:
 *
 * <pre>
 * def cc = new CompilerConfiguration()
 * cc.addCompilationCustomizers(new SandboxTransformer())
 * sh = new GroovyShell(cc)
 * </pre>
 *
 * <p>
 * By default, this code intercepts everything that can be intercepted, which are:
 * <ul>
 *     <li>Method calls (instance method and static method)
 *     <li>Object allocation (that is, a constructor call except of the form "this(...)" and "super(...)")
 *     <li>Property access (e.g., z=foo.bar, z=foo."bar") and assignment (e.g., foo.bar=z, foo."bar"=z)
 *     <li>Attribute access (e.g., z=foo.@bar) and assignments (e.g., foo.@bar=z)
 *     <li>Array access and assignment (z=x[y] and x[y]=z)
 * </ul>
 * <p>
 * You can disable interceptions selectively by setting respective {@code interceptXXX} flags to {@code false}.
 *
 * <p>
 * There'll be a substantial hit to the performance of the execution.
 *
 * @author Kohsuke Kawaguchi
 */
public class SandboxTransformer extends CompilationCustomizer {
    /**
     * Intercept method calls
     */
    boolean interceptMethodCall=true;
    /**
     * Intercept object instantiation by intercepting its constructor call.
     *
     * Note that Java byte code doesn't allow the interception of super(...) and this(...)
     * so the object instantiation by defining and instantiating a subtype cannot be intercepted.
     */
    boolean interceptConstructor=true;
    /**
     * Intercept property access for both read "(...).y" and write "(...).y=..."
     */
    boolean interceptProperty=true;
    /**
     * Intercept array access for both read "y=a[x]" and write "a[x]=y"
     */
    boolean interceptArray=true;
    /**
     * Intercept attribute access for both read "z=x.@y" and write "x.@y=z"
     */
    boolean interceptAttribute=true;

    public SandboxTransformer() {
        super(CompilePhase.CANONICALIZATION);
    }

    @Override
    public void call(final SourceUnit source, GeneratorContext context, ClassNode classNode) {
        if (classNode == null) { // TODO is this even possible? CpsTransformer implies it is not.
            return;
        }

        ClassCodeExpressionTransformer visitor = createVisitor(source, classNode);

        processConstructors(visitor, classNode);
        for (MethodNode m : classNode.getMethods()) {
            visitor.visitMethod(m);
        }
        for (Statement s : classNode.getObjectInitializerStatements()) {
            s.visit(visitor);
        }
        for (FieldNode f : classNode.getFields()) {
            visitor.visitField(f);
        }
    }

    /** Do not care about {@code super} calls for classes extending these types. */
    private static final Set<String> TRIVIAL_CONSTRUCTORS = new HashSet<>(Arrays.asList(
        Object.class.getName(),
        Script.class.getName(),
        "com.cloudbees.groovy.cps.SerializableScript",
        "org.jenkinsci.plugins.workflow.cps.CpsScript"));
    /**
     * Apply SECURITY-582 fix to constructors.
     */
    public void processConstructors(final ClassCodeExpressionTransformer visitor, ClassNode classNode) {
        ClassNode superClass = classNode.getSuperClass();
        List<ConstructorNode> declaredConstructors = classNode.getDeclaredConstructors();
        if (TRIVIAL_CONSTRUCTORS.contains(superClass.getName())) {
            for (ConstructorNode c : declaredConstructors) {
                visitor.visitMethod(c);
            }
        } else {
            if (declaredConstructors.isEmpty()) {
                ConstructorNode syntheticConstructor = new ConstructorNode(Modifier.PUBLIC, new BlockStatement());
                declaredConstructors = Collections.singletonList(syntheticConstructor);
                classNode.addConstructor(syntheticConstructor);
            } else {
                declaredConstructors = new ArrayList<>(declaredConstructors);
            }
            for (ConstructorNode c : declaredConstructors) {
                Statement code = c.getCode();
                List<Statement> body;
                if (code instanceof BlockStatement) {
                    body = ((BlockStatement) code).getStatements();
                } else {
                    body = Collections.singletonList(code);
                }
                TupleExpression superArgs = new TupleExpression();
                if (!body.isEmpty() && body.get(0) instanceof ExpressionStatement && ((ExpressionStatement) body.get(0)).getExpression() instanceof ConstructorCallExpression) {
                    ConstructorCallExpression cce = (ConstructorCallExpression) ((ExpressionStatement) body.get(0)).getExpression();
                    if (cce.isThisCall()) { // these are fine as is
                        visitor.visitMethod(c);
                        continue;
                    } else if (cce.isSuperCall()) {
                        body = body.subList(1, body.size());
                        superArgs = ((TupleExpression) cce.getArguments());
                    }
                }
                List<Expression> thisArgs = new ArrayList<>();
                final TupleExpression _superArgs = superArgs;
                final AtomicReference<Expression> superArgsTransformed = new AtomicReference<>();
                ((ScopeTrackingClassCodeExpressionTransformer) visitor).withMethod(c, new Runnable() {
                    @Override
                    public void run() {
                        superArgsTransformed.set(((VisitorImpl) visitor).transformArguments(_superArgs));
                    }
                });
                thisArgs.add(((VisitorImpl) visitor).makeCheckedCall("checkedSuperConstructor", new ClassExpression(superClass), superArgsTransformed.get()));
                Parameter[] origParams = c.getParameters();
                for (Parameter p : origParams) {
                    thisArgs.add(new VariableExpression(p));
                }
                c.setCode(new BlockStatement(new Statement[] {new ExpressionStatement(new ConstructorCallExpression(ClassNode.THIS, new TupleExpression(thisArgs)))}, c.getVariableScope()));
                Parameter[] params = new Parameter[origParams.length + 1];
                params[0] = new Parameter(new ClassNode(Checker.SuperConstructorWrapper.class), "$scw");
                System.arraycopy(origParams, 0, params, 1, origParams.length);
                List<Expression> scwArgs = new ArrayList<>();
                int x = 0;
                for (Expression superArg : superArgs) {
                    scwArgs.add(/*new CastExpression(superArg.getType(), */new MethodCallExpression(new VariableExpression("$scw"), "arg", new ConstantExpression(x++))/*)*/);
                }
                List<Statement> body2 = new ArrayList<>();
                body2.add(0, new ExpressionStatement(new ConstructorCallExpression(ClassNode.SUPER, new ArgumentListExpression(scwArgs))));
                for (final Statement s : body) {
                    ((ScopeTrackingClassCodeExpressionTransformer) visitor).withMethod(c, new Runnable() {
                        @Override
                        public void run() {
                            s.visit(visitor);
                        }
                    });
                    body2.add(s);
                }
                ConstructorNode c2 = new ConstructorNode(Modifier.PRIVATE, params, c.getExceptions(), new BlockStatement(body2, c.getVariableScope()));
                // perhaps more misleading than helpful: c2.setSourcePosition(c);
                classNode.addConstructor(c2);
            }
        }
    }

    @Deprecated
    public ClassCodeExpressionTransformer createVisitor(SourceUnit source) {
        return createVisitor(source, null);
    }
    
    public ClassCodeExpressionTransformer createVisitor(SourceUnit source, ClassNode clazz) {
        return new VisitorImpl(source, clazz, this);
    }


    /**
     * Checks if a {@link DeclarationExpression#getVariableExpression} might induce {@link DefaultTypeTransformation#castToType} to call a constructor.
     * If so, {@link Checker#checkedCast} should be run.
     * Will be false for example if the declared type is an array, {@code abstract}, or unspecified (just {@code def}).
     * Not yet supporting {@link DeclarationExpression#getTupleExpression} on LHS;
     * and currently ignoring {@link DeclarationExpression#getRightExpression} though some might not possibly be arrays, {@link Collection}s, or {@link Map}s.
     */
    public static boolean mightBePositionalArgumentConstructor(VariableExpression ve) {
        ClassNode type = ve.getType();
        if (type.isArray()) {
            return false; // do not care about componentType
        }
        Class clazz;
        try {
            clazz = type.getTypeClass();
        } catch (GroovyBugError x) {
            return false; // "ClassNode#getTypeClass for … is called before the type class is set" when assigning to a type defined in Groovy source
        }
        return clazz != null && clazz != Object.class && !Modifier.isAbstract(clazz.getModifiers());
    }

    static final Token ASSIGNMENT_OP = new Token(Types.ASSIGN, "=", -1, -1);

    static final ClassNode checkerClass = new ClassNode(Checker.class);
    static final ClassNode ScriptBytecodeAdapterClass = new ClassNode(ScriptBytecodeAdapter.class);

    /**
     * Expression that accesses the closure object itself from within the closure.
     *
     * Currently a hacky "asWritable().getOwner()"
     */
    static final Expression CLOSURE_THIS;

    static {
        MethodCallExpression aw = new MethodCallExpression(new VariableExpression("this"),"asWritable",EMPTY_ARGUMENTS);
        aw.setImplicitThis(true);

        CLOSURE_THIS = new MethodCallExpression(aw,"getOwner",EMPTY_ARGUMENTS);
    }

    public ClassNode getCheckerClass() {
        return checkerClass;
    }

    public boolean isInterceptMethodCall() {
        return interceptMethodCall;
    }

    public boolean isInterceptConstructor() {
        return interceptConstructor;
    }

    public boolean isInterceptProperty() {
        return interceptProperty;
    }

    public boolean isInterceptArray() {
        return interceptArray;
    }

    public boolean isInterceptAttribute() {
        return interceptAttribute;
    }
}
