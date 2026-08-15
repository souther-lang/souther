package souther.compiler.examples;

import souther.compiler.generated.MemoryClassLoader;
import souther.compiler.codegen.Backend;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.GeneratedClasses;

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
     * Applies {@code helper} to {@code args}, which are live values, by calling the method emitted
     * under {@code emittedAs}.
     *
     * <p>The two are apart because only one of them is the function. {@code emittedAs} is where the
     * method went and is the module's own business — a kernel's wrapper is emitted under a name no
     * source could spell — while {@code helper} is what the row applied, and it is what every report
     * from here names and what {@link #running()} answers with. Handed one name for both, the wrapper's
     * address would reach the author the moment a helper failed or ran out of time, which is the same
     * kind of leak as refusing a call for how it happens to be compiled.
     *
     * <p>A helper this module only expands has no method — which is what a helper whose body produces
     * a function is — and that is said as itself, so the rule that a fixture may apply a helper does
     * not appear to have exceptions nothing explains.
     */
    /**
     * Runs the method emitted for a row operand, which takes nothing and answers with the value that
     * operand is.
     *
     * <p>No name is registered while it runs. What was being evaluated is the row's own account of
     * itself and is not read back out of this class, and where execution has got to is the JVM's; a
     * register here would answer with the name of a method no source spells. That is what
     * {@link #running()} was for the reading this replaces, and it is not extended to this one.
     */
    Object run(String emittedAs) {
        return apply(null, emittedAs, new Object[0]);
    }

    Object invoke(String helper, String emittedAs, Object[] args) {
        String outer = running.get();   // a helper applied to a helper's argument nests
        running.set(helper);
        try {
            return apply(helper, emittedAs, args);
        } catch (InvocationFailure f) {
            throw RowFailures.of(f, "`" + helper + "`");
        } finally {
            running.set(outer);
        }
    }

    /**
     * Loads the method and applies it, turning what it ends with into what the row is told.
     *
     * <p>{@code named} is what a report from here calls what it ran, or null where nothing here
     * names it: an operand's method is the row's own value, and what the row was evaluating is said
     * by the row.
     */
    private Object apply(String named, String emittedAs, Object[] args) {
        String helper = named == null ? "the value the row writes" : named;
        Method method;
        try {
            Class<?> fns = GeneratedClasses.load(loader, new GeneratedClass.Helpers(module));
            Class<?>[] params = new Class<?>[args.length];
            Arrays.fill(params, Object.class);
            // Every emitted helper boxes its parameters and its result across the method boundary, so
            // the descriptor is Object-shaped whatever the helper's declared types are.
            method = fns.getDeclaredMethod(Backend.helperMethod(emittedAs), params);
            method.setAccessible(true);   // `$Fns` is package-private in every module (ADR-0075)
        } catch (ClassNotFoundException | NoSuchMethodException _) {
            throw FixtureException.cannotBeCalled(helper);
        }
        try {
            return method.invoke(null, args);
        } catch (InvocationTargetException ite) {
            // What the generated code ended with, carried out as it came. What it means — whether
            // the evaluation went over its budget, whether the stack ran out, whether the value the
            // row wanted simply is not there — is read where the row is evaluated, which is what
            // holds the phase and the position to say it against.
            throw new InvocationFailure(ite.getCause());
        } catch (ReflectiveOperationException e) {
            // Not the generated program failing: this compiler could not reach its own output.
            throw new FixtureException((named == null ? "the value the row writes"
                    : "`" + named + "`") + " could not be called: " + e.getMessage());
        }
    }

    /** The helper being applied, or null when the row is not inside one. */
    String running() {
        return running.get();
    }
}
