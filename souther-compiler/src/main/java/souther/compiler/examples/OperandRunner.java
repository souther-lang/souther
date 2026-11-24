package souther.compiler.examples;

import souther.compiler.generated.MemoryClassLoader;
import souther.compiler.codegen.Backend;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.GeneratedClasses;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.HashMap;
import java.util.Map;

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

    /**
     * The methods of a {@code $Fns} an operand can be emitted as — static, taking nothing — by
     * name, made callable once.
     *
     * <p>Filed once per class rather than looked up per operand. Every helper of the module is a
     * method of the one class, and finding one by name walks all of them: asked for every operand
     * of every row, that is the module's size again for each value a row writes. The class is the
     * loader's, and the loader is shared by every row of the module, so one filing serves them all
     * and goes when the loader does.
     */
    private static final ClassValue<Map<String, Method>> OPERANDS = new ClassValue<>() {
        @Override
        protected Map<String, Method> computeValue(Class<?> fns) {
            Map<String, Method> out = new HashMap<>();
            for (Method each : fns.getDeclaredMethods()) {
                if (each.getParameterCount() == 0 && Modifier.isStatic(each.getModifiers())) {
                    each.setAccessible(true);   // `$Fns` is package-private in every module
                    out.put(each.getName(), each);
                }
            }
            return Map.copyOf(out);
        }
    };

    /** Runs the method emitted under {@code emittedAs}, answering with the value it computed. */
    Object run(String emittedAs) {
        Method method;
        try {
            Class<?> fns = GeneratedClasses.load(loader, new GeneratedClass.Helpers(module));
            method = OPERANDS.get(fns).get(Backend.helperMethod(emittedAs));
        } catch (ClassNotFoundException _) {
            throw FixtureException.nothingWasEmittedFor();
        }
        if (method == null) {
            throw FixtureException.nothingWasEmittedFor();
        }
        try {
            return method.invoke(null);
        } catch (InvocationTargetException ite) {
            // What the generated code ended with, carried out as it came. What it means — whether
            // the evaluation went over its budget, whether the stack ran out, whether the value the
            // row wanted simply is not there — is read where the row is evaluated, which is what
            // holds the phase and the position to say it against. A class of this compile that will
            // not link is not something the evaluation ended with, and is said before it is carried.
            throw InvocationFailure.ofGeneratedCode(ite.getCause());
        } catch (ReflectiveOperationException e) {
            // Not the generated program failing: this compiler could not reach its own output.
            throw new FixtureException(
                    "the value the row writes could not be called: " + e.getMessage());
        }
    }
}
