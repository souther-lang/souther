package souther.compiler;

import souther.compiler.codegen.Backend;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.concurrent.atomic.AtomicReference;

/**
 * Runs a helper the way the module that compiled it runs it: the {@code static} method emitted on the
 * module's {@code $Fns} (ADR-0038), applied to values a fixture has already built (ADR-0077).
 *
 * <p>This is where an {@code example} meets the JVM — the class, the method name, the reflection and
 * what a failure inside the helper means — so the fixture that applies the helper does not have to
 * know any of it. What arrives here is a name and its arguments; what leaves is the value, or the
 * reason the row cannot state anything.
 *
 * <p>One instance belongs to one row's evaluation, because {@link #running()} is what the row's time
 * budget reads when the row does not finish, and that answer is that row's.
 */
final class HelperInvoker {

    private final String module;
    private final MemoryClassLoader loader;
    /** The helper being applied right now, read from the thread waiting on this row. */
    private final AtomicReference<String> running = new AtomicReference<>();

    HelperInvoker(String module, MemoryClassLoader loader) {
        this.module = module;
        this.loader = loader;
    }

    /**
     * Applies {@code name} to {@code args}, which are live values.
     *
     * <p>A helper this module only expands has no method — which is what a standard-library intrinsic
     * implemented in Java and a helper whose body produces a function are — and that is said as itself,
     * so the rule that a fixture may apply a helper does not appear to have exceptions nothing explains.
     */
    Object invoke(String name, Object[] args) {
        Method method;
        try {
            Class<?> fns = loader.loadClass(module + ".$Fns");
            Class<?>[] params = new Class<?>[args.length];
            Arrays.fill(params, Object.class);
            // Every emitted helper boxes its parameters and its result across the method boundary, so
            // the descriptor is Object-shaped whatever the helper's declared types are.
            method = fns.getDeclaredMethod(Backend.helperMethod(name), params);
            method.setAccessible(true);   // `$Fns` is package-private in every module (ADR-0075)
        } catch (ClassNotFoundException | NoSuchMethodException _) {
            throw new FixtureException("`" + name + "` cannot be called from an example fixture:"
                    + " it has no executable helper method");
        }
        String outer = running.get();   // a helper applied to a helper's argument nests
        running.set(name);
        try {
            return method.invoke(null, args);
        } catch (InvocationTargetException ite) {
            Throwable cause = ite.getCause();
            // The helper stopped itself, having gone through more than the evaluation was allowed.
            // That is about the budget and not about this helper's value, and it belongs to whoever
            // is holding the evaluation to that budget — read as a fixture that would not build, the
            // reason would be lost and the report would blame the wrong thing.
            if (cause instanceof souther.compiler.evaluate.StepLimitExceeded
                    || cause instanceof souther.compiler.evaluate.DepthLimitExceeded) {
                throw (RuntimeException) cause;
            }
            if (cause instanceof StackOverflowError) {
                // a non-tail `partial` recursion that does not terminate — not a value the row can state
                throw new NonTerminationException("`" + name + "` overflowed the stack");
            }
            throw new FixtureException("`" + name + "` did not produce a value: "
                    + (cause == null ? ite : cause.getMessage()));
        } catch (ReflectiveOperationException e) {
            throw new FixtureException("`" + name + "` could not be called: " + e.getMessage());
        } finally {
            running.set(outer);
        }
    }

    /** The helper being applied, or null when the row is not inside one. */
    String running() {
        return running.get();
    }
}
