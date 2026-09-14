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
 * The classes measure hands out no line, and what a behavior is owed at the lines is asked for by
 * name.
 *
 * <p>A behavior is measured against what it is owed a row for, and two of a border's four points can
 * be owed to the declarations that drew the line instead. The account used to sit inside the
 * partition evidence beside the classes, as a list of the points a body's own rules settled — and a
 * reader holding one of its entries could walk back to the border and read the roles beside it,
 * measuring a body against a row nothing written for it is owed. Now the account is the module's one
 * relation projected to the behavior ({@link Adequacy.BodyBorders}), whose membership is the
 * point's own answer ({@link BorderObligationPointAssessment#belongsToBehaviorAccount}), and the
 * classes measure holds nothing about a line at all. What a reader that shows a border whole reads
 * is {@link BehaviorEvidence#boundaryReadings}, and it asks for that by name too.
 *
 * <p>Read as a closure from the classes measure rather than as a list of what is allowed: a field
 * or a reader added later that reaches a line is caught by having been added, not by anybody
 * remembering to name it here.
 */
class ABehaviorsAccountDoesNotReachTheLinesOtherPointsTest {

    /** The vocabulary this walks, which is where an assessment could be reached from. Types outside
     *  it — a string, a list, a source id — hold nothing of this compiler's measures. */
    private static final Set<String> WALKED = Set.of(
            "souther.compiler.query", "souther.compiler.partition");

    @Test
    void nothingReachableFromTheClassesMeasureIsAnAccountOrAnAssessmentOfALine() {
        Set<Class<?>> reached = reachableFrom(PartitionEvidence.class);

        // The walk went somewhere. A closure that came back holding nothing would pass every
        // assertion below by having read no method at all.
        assertTrue(reached.contains(PartitionEvidence.AxisCoverage.class),
                () -> "the classes are what the measure hands out: " + named(reached));

        // A line itself stays reachable, through the cause a measurement carries when it could not
        // read a value at one ({@link Weakening.BorderValueUnreadable}). That is provenance about
        // why a measure is weaker than it looks, and naming the line is the whole of what it says;
        // what must not be here is an account of what a row at one is owed for.
        assertFalse(reached.contains(OwedBoundaryPoint.class),
                () -> "the classes measure reaches a place a row is composed at: "
                        + named(reached));
        assertFalse(reached.contains(BorderObligationPointAssessment.class),
                () -> "the classes measure reaches what a behavior is owed, which is asked for by"
                        + " name: " + named(reached));
        assertFalse(reached.contains(BorderAssessment.class),
                () -> "the classes measure reaches an assessment of a whole line: "
                        + named(reached));
        assertFalse(reached.contains(BorderAssessment.Point.class),
                () -> "the classes measure reaches a point of a line: " + named(reached));
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
