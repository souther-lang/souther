package souther.compiler.execute;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Prepared;
import souther.compiler.observe.Observations;

import java.lang.reflect.Method;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.lang.reflect.WildcardType;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the language asks an execution, and what it is told back, is the language's.
 *
 * <p>The rule #971 exists for, kept mechanically. An interface answering in the language's words and
 * asked in the machine's is not an inversion — it is the same dependency with a wider type on it —
 * so this walks what crosses in <em>both</em> directions and refuses the machine on either side. A
 * check on the answers alone would leave half of it standing, and half is what a convenience takes
 * first.
 *
 * <p>What is refused is the list the issue names: the store this compiler answers its own questions
 * in, a compilation, an artifact of emitted classes, a class loader, a generated class, and a bare
 * {@code Object}. Not what the compiler read the source into — {@code Hir}, {@code Symbols} and a
 * prepared module are how a program is settled here, and an execution of examples is over rows this
 * compiler never lowered, so refusing them would be refusing the question rather than the machine.
 * That is the difference between this walk and the one over a checked program, which does refuse
 * them, because what reads a checked program is an output standing outside this compiler.
 *
 * <p>The subsystem that runs a row on a worker of this compile's own is refused for the same reason
 * the emitted classes are. What a run is held to is the compile's and crosses as a term; the
 * arrangement that keeps it — a thread of a stated size, a wall clock, work handed back to the
 * caller — is one implementation's answer to how, and an execution that answers how differently
 * would have to name it to be asked at all.
 *
 * <p>Reachability and not the declared surface of one interface. A type is reached through the
 * methods of the types before it and through the arms of a sealed one, so a machine word four hops
 * out is one that crossed.
 */
class NothingCrossingTheExecutionBoundaryIsTheMachinesTest {

    /** What may not cross, in either direction. */
    private static final List<String> THE_MACHINES = List.of(
            "souther.compiler.query.Db",
            "souther.compiler.query.Compilation",
            "souther.compiler.generated.",
            "souther.compiler.jvm.",
            "souther.compiler.execute.jvm.",
            "souther.compiler.examples.",
            "java.lang.ClassLoader",
            "java.lang.Object");

    /**
     * Where the walk stops, and it is one place.
     *
     * <p>A diagnostic is what a reader is told. What it interpolates it carries by name, typed
     * {@code Object} because a message says a count in one entry and a type name in the next — so
     * walking into one finds an {@code Object} under every answer that reports anything, and the
     * rule that would quiet it is "a diagnostic may not cross", which refuses the report itself.
     *
     * <p>Nothing is lost by stopping. What that map holds is decided when the message is built and
     * no signature says what it is, so a walk could not have seen a machine word in there anyway.
     */
    private static final String THE_REPORT = "souther.compiler.diag.";

    @Test
    void nothingCrossingTheExecutionBoundaryIsTheMachines() {
        List<String> found = new ArrayList<>();
        for (Reached reached : everythingCrossing(ProgramExecution.class)) {
            for (String machine : THE_MACHINES) {
                if (reached.type().getName().equals(machine)
                        || reached.type().getName().startsWith(machine)) {
                    found.add(reached.type().getName() + " via " + reached.how());
                }
            }
        }

        assertEquals(List.of(), found,
                "an execution that is not the JVM's would have to know these to be asked, or to"
                        + " answer");
    }

    /**
     * And the walk reaches what actually crosses.
     *
     * <p>A walk that got nowhere would answer the same as one that got everywhere and found
     * nothing. These are the two ends of it — what the language hands over and what it is told back
     * — and both are several hops in.
     */
    @Test
    void andTheWalkGoesThroughWhatIsAskedAndWhatIsAnswered() {
        List<String> reached = everythingCrossing(ProgramExecution.class).stream()
                .map(each -> each.type().getName()).toList();

        // Named by their classes and not by how they are spelled: a rename would otherwise leave
        // this looking for a type nothing declares any more, and a walk that had stopped reaching
        // it would read the same as the rename.
        assertTrue(reached.contains(Prepared.ForExamples.class.getName()),
                () -> "no prepared examples in " + reached);
        assertTrue(reached.contains(Observations.class.getName()),
                () -> "no observations in " + reached);
        assertTrue(reached.size() > 30, () -> "the walk reached only " + reached.size());
    }

    /** A type that crosses, and the shortest way it got there — so a failure says where to look
     *  rather than that something, somewhere, is wrong. */
    private record Reached(Class<?> type, String how) {}

    private static List<Reached> everythingCrossing(Class<?> from) {
        List<Reached> reached = new ArrayList<>();
        Set<Class<?>> seen = new LinkedHashSet<>();
        Deque<Reached> pending = new ArrayDeque<>();
        pending.add(new Reached(from, from.getSimpleName()));
        while (!pending.isEmpty()) {
            Reached here = pending.poll();
            if (!seen.add(here.type())) {
                continue;
            }
            reached.add(here);
            for (Reached next : outOf(here)) {
                // Walked on through only where this compiler declared it. A `java.util.List` has
                // methods of its own and none of them is a way out of here; what matters about one
                // is its element, which `namedIn` already produced.
                if (next.type().getName().startsWith("souther.")
                        && !next.type().getName().startsWith(THE_REPORT)) {
                    pending.add(next);
                } else if (!seen.contains(next.type())) {
                    // Reached and not walked through: it is still checked for being one of the
                    // machine's, and a diagnostic is not.

                    seen.add(next.type());
                    reached.add(next);
                }
            }
        }
        return reached;
    }

    private static List<Reached> outOf(Reached here) {
        List<Reached> out = new ArrayList<>();
        // An arm of a sum a caller switches over is a type it is handed.
        Class<?>[] arms = here.type().getPermittedSubclasses();
        if (arms != null) {
            for (Class<?> arm : arms) {
                out.add(new Reached(arm, here.how() + " -> case " + arm.getSimpleName()));
            }
        }
        for (Method method : here.type().getMethods()) {
            if (isEveryTypes(method)) {
                continue;
            }
            String at = here.how() + "." + method.getName() + "()";
            for (Class<?> named : namedIn(method.getGenericReturnType())) {
                out.add(new Reached(named, at));
            }
            for (Type parameter : method.getGenericParameterTypes()) {
                for (Class<?> named : namedIn(parameter)) {
                    out.add(new Reached(named, at + " parameter"));
                }
            }
        }
        return out;
    }

    /**
     * Whether {@code method} is one every type has rather than one this type crosses with.
     *
     * <p>Asked of the shape and not of who declared it. A record declares its own {@code equals},
     * so a walk that skipped {@code Object}'s declarations alone found {@code equals(Object)} on
     * every record it reached and called the {@code Object} a value that crossed — which is the
     * walk being wrong about a boundary that is fine, and the kind of finding that gets a real rule
     * loosened to quiet it.
     */
    private static boolean isEveryTypes(Method method) {
        if (method.isBridge() || method.isSynthetic()) {
            // What the compiler wrote to make a generic method callable through an erased one. An
            // enum's `compareTo` arrives as `compareTo(Object)` this way, and that `Object` is a
            // fact about erasure rather than about what the boundary hands over.
            return true;
        }
        try {
            Object.class.getMethod(method.getName(), method.getParameterTypes());
            return true;
        } catch (NoSuchMethodException _) {
            return false;
        }
    }

    /**
     * Every class a written type names, the arguments of a generic one included.
     *
     * <p>{@code List<Diagnostic>} names a list and a diagnostic, and it is the second that matters:
     * something inside a collection crosses exactly as easily as a bare one.
     *
     * <p>Everything, and not this compiler's alone. A class loader and a bare {@code Object} are
     * two of the things that may not cross, and both are the platform's.
     */
    private static List<Class<?>> namedIn(Type type) {
        List<Class<?>> named = new ArrayList<>();
        switch (type) {
            case Class<?> c -> {
                Class<?> element = c;
                while (element.isArray()) {
                    element = element.getComponentType();
                }
                if (!element.isPrimitive()) {
                    named.add(element);
                }
            }
            case ParameterizedType p -> {
                named.addAll(namedIn(p.getRawType()));
                for (Type argument : p.getActualTypeArguments()) {
                    named.addAll(namedIn(argument));
                }
            }
            case WildcardType w -> {
                for (Type bound : w.getUpperBounds()) {
                    named.addAll(namedIn(bound));
                }
            }
            default -> { }
        }
        return named;
    }
}
