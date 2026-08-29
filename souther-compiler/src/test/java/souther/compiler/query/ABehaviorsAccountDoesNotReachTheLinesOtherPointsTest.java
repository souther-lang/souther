package souther.compiler.query;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.lang.reflect.WildcardType;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a behavior's account hands out does not reach the points beside the ones in it.
 *
 * <p>A behavior is measured against what it is owed a row for, and two of a border's four points can
 * be owed to the declarations that drew the line instead. Naming the account {@code owes} says which
 * question it answers; it does not stop a reader holding one of its entries from walking back to the
 * border and reading the roles beside it, and a reader that did would be measuring a body against a
 * row nothing written for it is owed — which is the whole of what this account exists to prevent.
 *
 * <p>So an entry carries the line and not the assessment of it. The line is what a report writes
 * about a point — the position, the rule, what the point asks for — and what became of the border's
 * other roles is no part of it. What a reader that shows a border whole reads is
 * {@link BehaviorEvidence#boundaryReadings}, and it asks for that by name.
 *
 * <p>Read as a closure from the account rather than as a list of what is allowed: a field or a
 * reader added later that reaches an assessment is caught by having been added, not by anybody
 * remembering to name it here.
 */
class ABehaviorsAccountDoesNotReachTheLinesOtherPointsTest {

    /** The vocabulary this walks, which is where an assessment could be reached from. Types outside
     *  it — a string, a list, a source id — hold nothing of this compiler's measures. */
    private static final Set<String> WALKED = Set.of(
            "souther.compiler.query", "souther.compiler.partition");

    @Test
    void nothingReachableFromWhatABehaviorIsOwedIsAnAssessmentOfALine() {
        Set<Class<?>> reached = reachableFrom(PartitionEvidence.class);

        // The walk went somewhere. A closure that came back holding nothing would pass every
        // assertion below by having read no method at all.
        assertTrue(reached.contains(OwedBoundaryPoint.class),
                () -> "the account is what a behavior's evidence hands out: " + named(reached));
        assertTrue(reached.contains(souther.compiler.partition.Border.class),
                () -> "and an entry carries the line it is a point of: " + named(reached));

        assertFalse(reached.contains(BorderAssessment.class),
                () -> "a behavior's account reaches an assessment of a whole line: "
                        + named(reached));
        assertFalse(reached.contains(BorderAssessment.Point.class),
                () -> "a behavior's account reaches a point of one it may not be measured for: "
                        + named(reached));
    }

    /** Every type this compiler's own vocabulary reaches from {@code from}, through what its public
     *  readers answer with. */
    private static Set<Class<?>> reachableFrom(Class<?> from) {
        Set<Class<?>> found = new LinkedHashSet<>();
        Deque<Class<?>> left = new ArrayDeque<>();
        left.add(from);
        while (!left.isEmpty()) {
            Class<?> each = left.removeFirst();
            if (!found.add(each)) {
                continue;
            }
            for (Method method : each.getMethods()) {
                if (Modifier.isStatic(method.getModifiers())) {
                    continue;   // a factory is not something a value in hand hands out
                }
                for (Class<?> answered : namedIn(method.getGenericReturnType())) {
                    if (ours(answered)) {
                        left.add(answered);
                    }
                }
            }
            // The arms of a sum are reached by reading one, so they are part of what it hands out.
            for (Class<?> arm : each.getPermittedSubclasses() == null
                    ? new Class<?>[0] : each.getPermittedSubclasses()) {
                if (ours(arm)) {
                    left.add(arm);
                }
            }
        }
        return found;
    }

    /** The classes a type names, itself and whatever it is written over. */
    private static Set<Class<?>> namedIn(Type type) {
        Set<Class<?>> out = new LinkedHashSet<>();
        switch (type) {
            case Class<?> named -> out.add(named);
            case ParameterizedType over -> {
                out.addAll(namedIn(over.getRawType()));
                for (Type argument : over.getActualTypeArguments()) {
                    out.addAll(namedIn(argument));
                }
            }
            case WildcardType any -> {
                for (Type bound : any.getUpperBounds()) {
                    out.addAll(namedIn(bound));
                }
            }
            default -> { }
        }
        return out;
    }

    private static boolean ours(Class<?> type) {
        return type.getPackage() != null && WALKED.contains(type.getPackage().getName());
    }

    private static Set<String> named(Set<Class<?>> types) {
        Set<String> out = new LinkedHashSet<>();
        types.forEach(each -> out.add(each.getSimpleName()));
        return out;
    }
}
