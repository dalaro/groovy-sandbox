package org.kohsuke.groovy.sandbox.robot

import junit.framework.TestCase
import org.codehaus.groovy.control.CompilerConfiguration

import org.kohsuke.groovy.sandbox.SandboxTransformer
import org.kohsuke.groovy.sandbox.impl.InterceptorRegistry

/**
 *
 *
 * @author Kohsuke Kawaguchi
 */
class RobotTest extends TestCase {
    Robot robot;
    GroovyShell sh;
    RobotSandbox sandbox = new RobotSandbox()

    @Override
    protected void setUp() {
        def cc = new CompilerConfiguration()
        cc.addCompilationCustomizers(new SandboxTransformer())
        def binding = new Binding();
        binding.robot = robot = new Robot();
        sh = new GroovyShell(binding,cc)

        InterceptorRegistry.getInstance().register(sandbox);
    }

    @Override
    protected void tearDown() {
        InterceptorRegistry.getInstance().unregister(sandbox);
    }

    void assertFail(String script) {
        try {
            sh.evaluate(script)
            fail("Should have failed");
        } catch (SecurityException e) {
            // as expected
        }
    }

    void eval(String script) {
        sh.evaluate(script)
    }

    void test1() {
        // these are OK
        eval("robot.leftArm.wave(3)")
        eval("[robot.@leftArm,robot.@rightArm]*.wave(3)")
        eval("if (robot.leftArm!=null) robot.leftArm.wave(1)")
        eval("def c = { x -> x.leftArm.wave(3) }; c(robot);")

        // these are not
        assertFail("robot.brain")
        assertFail("robot.@brain")
        assertFail("robot['brain']")
        assertFail("System.exit(-1)")
        assertFail("def c = { -> delegate = System; exit(-1) }; c();")
        assertFail("Class.forName('java.lang.String')")
        assertFail("'foo'.class.name")
        assertFail("new java.awt.Point(1,2)")
    }
}
