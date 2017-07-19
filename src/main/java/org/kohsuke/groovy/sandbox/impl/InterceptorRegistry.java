package org.kohsuke.groovy.sandbox.impl;

import org.kohsuke.groovy.sandbox.GroovyInterceptor;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.concurrent.CopyOnWriteArrayList;

/**
 * GroovyInterceptor instances are registered to the registry and retreived from the InvokerChain.
 */
public final class InterceptorRegistry {

    private static final InterceptorRegistry INSTANCE = new InterceptorRegistry();

    private final List<GroovyInterceptor> interceptorList = new CopyOnWriteArrayList<GroovyInterceptor>();

    private final ThreadLocal<List<GroovyInterceptor>> threadLocalInterceptors = new ThreadLocal<List<GroovyInterceptor>>() {
        @Override
        protected List<GroovyInterceptor> initialValue() {
            return new CopyOnWriteArrayList<GroovyInterceptor>();
        }
    };

    public final void register(GroovyInterceptor interceptor) {
        interceptorList.add(interceptor);
    }

    public final void unregister(GroovyInterceptor interceptor) {
        interceptorList.remove(interceptor);
    }

    public void registerThreadLocal(GroovyInterceptor interceptor) {
        threadLocalInterceptors.get().add(interceptor);
    }

    public void unregisterThreadLocal(GroovyInterceptor interceptor) {
        threadLocalInterceptors.get().remove(interceptor);
    }

    /**
     * Return any Global and ThreadLocal interceptors
     * @return
     */
    public Iterator<GroovyInterceptor> getApplicableInterceptors() {
        List<GroovyInterceptor> threadLocals = threadLocalInterceptors.get();
        if(threadLocals.size() > 0) {

            if(interceptorList.size() > 0 ){
                List<GroovyInterceptor> interceptors = new ArrayList<GroovyInterceptor>(threadLocals.size() + interceptorList.size());
                interceptors.addAll(interceptorList);
                interceptors.addAll(threadLocals);

                return interceptors.iterator();
            } else {
                return threadLocals.iterator();
            }

        } else {
            return interceptorList.iterator();
        }
    }
    public static final InterceptorRegistry getInstance() {
        return INSTANCE;
    }
}
