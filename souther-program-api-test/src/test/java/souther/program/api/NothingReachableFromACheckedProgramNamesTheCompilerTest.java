package souther.program.api;

import souther.compiler.program.CheckedProgram;

import org.junit.jupiter.api.Test;

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
 * Nothing an output can reach from a checked program is a piece of this compiler.
 *
 * <p>The rule the boundary exists for, kept mechanically rather than by reading. A single
 * convenience — {@code public Hir.Module lowered()}, {@code public Db db()} — puts the query graph
 * or the syntax tree back into what an output outside {@code souther-compiler} compiles against,
 * and after that the artifact cannot be separated again without breaking whoever took it.
 *
 * <p>Reachability and not the declared surface of one class. A type is reached through the methods
 * of the types before it, and through the arms of a sealed one, so a leak two hops down is a leak.
 */
class NothingReachableFromACheckedProgramNamesTheCompilerTest {

    /** How this compiler answers its own questions, what it emits with, what it parsed into, and
     *  how it decided. None of the four is a fact about a Souther program.
     *
     *  <p>{@code check} is on the list since #1080. What a behavior declares of its answer and what
     *  must hold of a value of a data are decisions the language makes, and the values that carry
     *  them used to be the check's own — reachable here without naming anything on this list, and
     *  holding a syntax tree two hops down. They are {@code core} values now, and this is what says
     *  the next one will be too. */
    private static final List<String> THE_COMPILERS_OWN = List.of(
            "souther.compiler.query.",
            "souther.compiler.codegen.",
            "souther.compiler.check.",
            "souther.compiler.ast.");

    /**
     * And the walk above reaches what an output actually reads.
     *
     * <p>A walk that got nowhere would answer the same as one that got everywhere and found
     * nothing. These are the two an output emits from, both several hops in, so reaching them says
     * the walk goes through the model rather than stopping at its first type.
     */
    @Test
    void andTheWalkGoesThroughWhatAnOutputEmitsFrom() {
        List<String> reached = everythingReachableFrom(CheckedProgram.class).stream()
                .map(each -> each.type().getName()).toList();

        assertTrue(reached.contains("souther.compiler.core.Core"), () -> "no Core in " + reached);
        assertTrue(reached.contains("souther.compiler.core.Composition"),
                () -> "no Composition in " + reached);
        // And the two conditions the language states, which are what #1080 put here. Each is
        // reached through the arm that carries it — a clause off a product, a rule off what a
        // behavior declares — which is the walk going through the model rather than past it.
        assertTrue(reached.contains("souther.compiler.core.ValueShape$Invariant"),
                () -> "no invariant clause in " + reached);
        assertTrue(reached.contains("souther.compiler.core.Contract$Rule"),
                () -> "no ensures rule in " + reached);
        assertTrue(reached.size() > 50, () -> "the walk reached only " + reached.size());
    }

    @Test
    void nothingReachableFromACheckedProgramNamesTheCompiler() {
        List<String> found = new ArrayList<>();
        for (Reached reached : everythingReachableFrom(CheckedProgram.class)) {
            for (String own : THE_COMPILERS_OWN) {
                if (reached.type().getName().startsWith(own)) {
                    found.add(reached.type().getName() + " via " + reached.how());
                }
            }
        }

        assertEquals(List.of(), found,
                "an output outside this compiler would have to name these to read a program");
    }

    /** A type an output can get to, and the shortest way it was got to — so a failure says where to
     *  look rather than that something, somewhere, is wrong. */
    private record Reached(Class<?> type, String how) {}

    private static List<Reached> everythingReachableFrom(Class<?> from) {
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
                pending.add(next);
            }
        }
        return reached;
    }

    private static List<Reached> outOf(Reached here) {
        List<Reached> out = new ArrayList<>();
        // An arm of a sum an output switches over is a type it holds.
        Class<?>[] arms = here.type().getPermittedSubclasses();
        if (arms != null) {
            for (Class<?> arm : arms) {
                out.add(new Reached(arm, here.how() + " -> case " + arm.getSimpleName()));
            }
        }
        for (Method method : here.type().getMethods()) {
            if (method.getDeclaringClass() == Object.class) {
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
     * Every class a written type names, the arguments of a generic one included.
     *
     * <p>{@code List<CheckedModule>} names a list and a module, and it is the second that matters:
     * a leak inside a collection is reached exactly as easily as a bare one.
     */
    private static List<Class<?>> namedIn(Type type) {
        List<Class<?>> named = new ArrayList<>();
        switch (type) {
            case Class<?> c -> {
                Class<?> element = c;
                while (element.isArray()) {
                    element = element.getComponentType();
                }
                if (element.getName().startsWith("souther.")) {
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
