package souther.compiler.publish;

import org.junit.jupiter.api.Test;

import souther.compiler.report.AdequacyReport;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.RecordComponent;
import java.lang.reflect.Type;
import java.lang.reflect.WildcardType;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Nothing a report is handed carries a kind of reason without the order it is said in.
 *
 * <p>What the orders themselves cannot say. A kind is put in order in one place and there is one
 * way to select from it — and a value that reaches a report holding a bare set of that kind has
 * gone round both, leaving the report to take an order from whatever the set iterates in.
 *
 * <p>So the population is the values a report can reach, and it is walked rather than listed: from
 * the report, through what its fields and components hold, into every arm of every sum on the way.
 * A value added between the two arrives here without anybody adding a line, and one that carries a
 * kind of reason as a collection is named.
 *
 * <p><b>Kinds of reason and not collections.</b> What is refused is a plurality of a kind that has
 * an order, because that is the plurality a report puts in a sentence. A list of anything else is
 * a sequence whose order is its own — the modules of a compilation are answered in the order their
 * sources were given — and has nothing to do with this.
 */
class NoReasonReachesAReportUnorderedTest {

    @Test
    void noKindWithAnOrderReachesAReportAsACollection() {
        List<String> found = new ArrayList<>();
        Set<Class<?>> kinds = kindsWithAnOrder();
        Set<Class<?>> seen = new LinkedHashSet<>();
        Deque<Class<?>> left = new ArrayDeque<>(List.of(AdequacyReport.class));
        while (!left.isEmpty()) {
            Class<?> here = left.removeFirst();
            if (!seen.add(here)) {
                continue;
            }
            for (Class<?> arm : here.isSealed() ? here.getPermittedSubclasses() : new Class<?>[0]) {
                left.addLast(arm);
            }
            for (Member each : membersOf(here)) {
                if (each.type() instanceof ParameterizedType held
                        && Collection.class.isAssignableFrom(rawOf(held.getRawType()))
                        && kinds.contains(rawOf(held.getActualTypeArguments()[0]))) {
                    found.add(here.getSimpleName() + "." + each.name() + " holds "
                            + rawOf(held.getActualTypeArguments()[0]).getSimpleName()
                            + " without the order it is said in");
                }
                for (Class<?> reached : typesIn(each.type())) {
                    if (reached.getPackageName().startsWith("souther.compiler")) {
                        left.addLast(reached);
                    }
                }
            }
        }

        // The walk reaches what this is about, said out loud. A walk that stopped early would find
        // nothing to name and pass for the reason a clean one does.
        assertTrue(seen.contains(souther.compiler.query.EstablishmentGap.Observation.class)
                        && seen.contains(souther.compiler.query.ObligationDisposition
                                .NotCounted.class),
                () -> "the walk does not reach the values this is about, so what it found is not"
                        + " what a report can be handed: " + seen.size() + " types reached");
        assertEquals(List.of(), found,
                "a report is handed a kind of reason with no order, and what it says them in will"
                        + " be whatever the collection iterates in");
    }

    /** Every kind something is published in an order of. */
    private static Set<Class<?>> kindsWithAnOrder() {
        Set<Class<?>> out = new LinkedHashSet<>();
        for (Field each : PublicationOrders.class.getDeclaredFields()) {
            if (!each.getType().equals(CanonicalSelection.Order.class)) {
                continue;
            }
            each.setAccessible(true);
            try {
                Object first = ((CanonicalSelection.Order<?>) each.get(null)).slots().getFirst();
                out.add(switch (first) {
                    case Class<?> arm -> sealedOver(arm);
                    case Enum<?> constant -> constant.getDeclaringClass();
                    default -> sealedOver(first.getClass());
                });
            } catch (IllegalAccessException opaque) {
                throw new AssertionError("an order this test cannot read: " + each.getName());
            }
        }
        assertTrue(out.size() > 1, "the kinds are read off the orders, and this found none");
        return out;
    }

    private static Class<?> sealedOver(Class<?> arm) {
        for (Class<?> each : arm.getInterfaces()) {
            if (each.isSealed()) {
                return each;
            }
        }
        return arm;
    }

    /**
     * What a value of {@code type} hands over.
     *
     * <p>What it holds and what it answers. A report reaches most of what it prints by asking —
     * {@code owed.disposition()}, {@code border.at(role)} — so a walk over fields alone reaches the
     * report's own shape and stops at the first interface, which is where everything this is about
     * begins.
     */
    private static List<Member> membersOf(Class<?> type) {
        List<Member> out = new ArrayList<>();
        if (type.isRecord()) {
            for (RecordComponent each : type.getRecordComponents()) {
                out.add(new Member(each.getName(), each.getGenericType()));
            }
        } else {
            for (Field each : type.getDeclaredFields()) {
                if (!Modifier.isStatic(each.getModifiers())) {
                    out.add(new Member(each.getName(), each.getGenericType()));
                }
            }
        }
        for (Method each : type.getMethods()) {
            if (each.getParameterCount() == 0 && !each.getReturnType().equals(void.class)
                    && !each.getDeclaringClass().equals(Object.class)) {
                out.add(new Member(each.getName() + "()", each.getGenericReturnType()));
            }
        }
        return out;
    }

    /** Every class named anywhere in {@code type}, itself and what it is parameterised by. */
    private static List<Class<?>> typesIn(Type type) {
        List<Class<?>> out = new ArrayList<>();
        switch (type) {
            case Class<?> it -> out.add(it.isArray() ? it.getComponentType() : it);
            case ParameterizedType it -> {
                out.addAll(typesIn(it.getRawType()));
                for (Type each : it.getActualTypeArguments()) {
                    out.addAll(typesIn(each));
                }
            }
            case WildcardType it -> {
                for (Type each : it.getUpperBounds()) {
                    out.addAll(typesIn(each));
                }
            }
            default -> { }
        }
        return out;
    }

    /** One thing a value holds, said the same way for a record and for a class. */
    private record Member(String name, Type type) {}

    private static Class<?> rawOf(Type type) {
        return type instanceof ParameterizedType it ? rawOf(it.getRawType())
                : type instanceof Class<?> it ? it : Object.class;
    }
}
