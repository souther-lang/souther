package souther.compiler.examples;

import souther.compiler.generated.MemoryClassLoader;
import souther.compiler.codegen.Backend;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.GeneratedClasses;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

/**
 * Runs the method a row's operand was emitted as: a {@code static} method on the module's
 * {@code $Fns} (ADR-0038) taking nothing and answering with the value that operand is.
 *
 * <p>This is where an {@code example} meets the JVM — the class, the method name, the reflection and
 * what a failure inside it means — so the reading that builds a row does not have to know any of it.
 *
 * <p>Nothing here names what ran. The operand is the row's own account of itself and is what every
 * report from the row quotes; the method it was emitted under is the module's own business, under a
 * name no source could spell, and an address like that reaching an author is the same kind of leak
 * as refusing a call for how it happens to be compiled.
 *
 * <p>One instance belongs to one row's evaluation, which is what its loader belongs to.
 */
final class OperandRunner {

    private final String module;
    private final MemoryClassLoader loader;

    OperandRunner(String module, MemoryClassLoader loader) {
        this.module = module;
        this.loader = loader;
    }

    /** Runs the method emitted under {@code emittedAs}, answering with the value it computed. */
    Object run(String emittedAs) {
        Method method;
        try {
            Class<?> fns = GeneratedClasses.load(loader, new GeneratedClass.Helpers(module));
            method = fns.getDeclaredMethod(Backend.helperMethod(emittedAs));
            method.setAccessible(true);   // `$Fns` is package-private in every module (ADR-0075)
        } catch (ClassNotFoundException | NoSuchMethodException _) {
            throw FixtureException.nothingWasEmittedFor();
        }
        try {
            return method.invoke(null);
        } catch (InvocationTargetException ite) {
            // What the generated code ended with, carried out as it came. What it means — whether
            // the evaluation went over its budget, whether the stack ran out, whether the value the
            // row wanted simply is not there — is read where the row is evaluated, which is what
            // holds the phase and the position to say it against.
            throw new InvocationFailure(ite.getCause());
        } catch (ReflectiveOperationException e) {
            // Not the generated program failing: this compiler could not reach its own output.
            throw new FixtureException(
                    "the value the row writes could not be called: " + e.getMessage());
        }
    }
}
