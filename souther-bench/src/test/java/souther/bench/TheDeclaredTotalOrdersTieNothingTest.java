package souther.bench;

import org.junit.jupiter.api.Test;

import souther.bench.SaltedOrderVocabulary.Signature;
import souther.compiler.inputs.Case;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.partition.AxisId;
import souther.compiler.partition.ClassOfAPosition;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * An order the reading takes as total ties nothing that is not equal.
 *
 * <p>A sort is a crossing only as far as its comparator separates every two elements that differ:
 * a stable sort leaves what it ties in the order the walk gave, so a comparator that ties two
 * unequal things puts nothing in an order. Which comparators the reading trusts is a list, and a
 * list is a claim, so each is put to a population that includes what makes it fail if it does:
 * two values spelled alike and not equal.
 *
 * <p>Every order that is declared has a population here, or this fails, so an order added to the
 * reading is put to the test it stands on.
 */
class TheDeclaredTotalOrdersTieNothingTest {

    @Test
    void everyDeclaredOrderHasAPopulationThatIncludesValuesSpelledAlikeAndUnequal() throws Exception {
        Map<String, List<Object>> populations = populations();
        List<String> without = new ArrayList<>();
        for (Signature each : SaltedOrderVocabulary.declaredTotalOrders()) {
            if (!populations.containsKey(each.owner())) {
                without.add(each.spelled());
            }
        }
        assertEquals(List.of(), without,
                "an order the reading takes as total has no population to be tested on");

        for (Map.Entry<String, List<Object>> each : populations.entrySet()) {
            assertFalse(spelledAlikeAndUnequal(each.getValue()).isEmpty(),
                    () -> "the population of " + each.getKey() + " has no two values spelled"
                            + " alike and unequal, so it cannot tell a spelled order from a"
                            + " structural one");
        }
    }

    @Test
    void noTwoValuesThatAreNotEqualAreTiedByADeclaredOrder() throws Exception {
        Map<String, List<Object>> populations = populations();
        for (Signature declared : SaltedOrderVocabulary.declaredTotalOrders()) {
            Method method = Class.forName(declared.owner().replace('/', '.'))
                    .getMethod(declared.name());
            @SuppressWarnings("unchecked")
            Comparator<Object> order = (Comparator<Object>) method.invoke(null);
            List<Object> population = populations.get(declared.owner());
            for (Object one : population) {
                for (Object other : population) {
                    int forward = order.compare(one, other);
                    assertEquals(one.equals(other), forward == 0,
                            () -> declared.spelled() + " ties " + one + " and " + other
                                    + " though they are not equal, or parts equal ones");
                    assertEquals(Integer.signum(forward), -Integer.signum(order.compare(other, one)),
                            () -> declared.spelled() + " does not order " + one + " and " + other
                                    + " the same way from both sides");
                    for (Object third : population) {
                        if (forward < 0 && order.compare(other, third) < 0) {
                            assertFalse(order.compare(one, third) >= 0,
                                    () -> declared.spelled() + " is not transitive over " + one
                                            + ", " + other + " and " + third);
                        }
                    }
                }
            }
        }
    }

    private static List<Object> spelledAlikeAndUnequal(List<Object> population) {
        List<Object> found = new ArrayList<>();
        for (Object one : population) {
            for (Object other : population) {
                if (!one.equals(other) && one.toString().equals(other.toString())) {
                    found.add(one);
                }
            }
        }
        return found;
    }

    private static Map<String, List<Object>> populations() {
        Map<String, List<Object>> out = new LinkedHashMap<>();
        out.put(TermPath.class.getName().replace('.', '/'), paths());
        out.put(ClassOfAPosition.class.getName().replace('.', '/'), classes());
        return out;
    }

    private static List<Object> paths() {
        List<Object> out = new ArrayList<>();
        out.add(TermPath.of("some"));
        out.add(TermPath.of("some").then("value"));
        out.add(TermPath.of("some").element());
        out.add(TermPath.of("some").refine(Refinement.of(new Case.Presence(true))));
        out.add(TermPath.of("some").refine(Refinement.of(new Case.Presence(false))));
        out.add(TermPath.of("some").refine(Refinement.of(new Case.SumCase(
                TypeSymbols.declared(new TypeKey("g", "Some")), false))));
        out.add(TermPath.of("some").refine(Refinement.of(new Case.SumCase(
                TypeSymbols.declared(new TypeKey("h", "Some")), false))));
        out.add(TermPath.of("some").refine(Refinement.of(new Case.Presence(true))).then("value"));
        out.add(TermPath.of("some").then("value").element());
        out.add(TermPath.of("other"));
        return out;
    }

    private static List<Object> classes() {
        List<Object> out = new ArrayList<>();
        for (AxisId axis : List.of(new AxisId("a/b", "c"), new AxisId("a", "b/c"),
                new AxisId("a", "c"), new AxisId("b", "c"))) {
            for (String id : List.of("x", "y")) {
                out.add(new ClassOfAPosition(axis, id));
            }
        }
        return out;
    }
}
