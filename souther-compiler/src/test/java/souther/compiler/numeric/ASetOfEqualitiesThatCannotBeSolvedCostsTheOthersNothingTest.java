package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Equalities that share no position are solved apart. A set that contradicts itself, or takes more
 * work than {@link ReducedRules#MOST_UPDATES} allows, is left as the equalities it was, and the
 * others are solved all the same.
 */
class ASetOfEqualitiesThatCannotBeSolvedCostsTheOthersNothingTest {

    private static final CanonicalOrder<String> ORDER = CanonicalOrder.asTheyAreSpelled();

    private static Map<String, ExactRatio> weighing(Object... pairs) {
        Map<String, ExactRatio> out = new LinkedHashMap<>();
        for (int i = 0; i < pairs.length; i += 2) {
            out.put((String) pairs[i], ExactRatio.of((Integer) pairs[i + 1]));
        }
        return out;
    }

    private static AffineConstraint<String> equality(Map<String, ExactRatio> coefs, long at) {
        return new AffineConstraint.Equality<>(new CanonicalForm<>(coefs), ExactRatio.of(at));
    }

    private static ReducedRules.Goal<String> goal(String position) {
        return new ReducedRules.Goal<>(weighing(position, 1), ExactRatio.ZERO);
    }

    /** {@code x = a + b}, a set of its own. */
    private static final AffineConstraint<String> SMALL = equality(weighing("x", 1, "a", -1, "b", -1), 0);

    /**
     * A chain {@code p0 = p1 + q0, p1 = p2 + q1, …}, one set whose solving updates a weight for
     * every pair of equalities and so outgrows any bound on the work.
     */
    private static List<AffineConstraint<String>> chain(int length) {
        List<AffineConstraint<String>> out = new ArrayList<>();
        for (int i = 0; i < length; i++) {
            out.add(equality(weighing("p" + i, 1, "p" + (i + 1), -1, "q" + i, -1), 0));
        }
        return out;
    }

    @Test
    void aSetTakingMoreWorkThanTheBoundIsLeftAsItWasAndTheOthersAreSolved() {
        List<AffineConstraint<String>> rules = new ArrayList<>(chain(400));
        rules.add(SMALL);

        ReducedRules<String> reduced = ReducedRules.of(rules, ORDER);

        assertNotNull(reduced);
        assertEquals(Map.of("a", ExactRatio.ONE, "b", ExactRatio.ONE),
                reduced.put(goal("x")).coefs(), "x = a + b is solved");
        assertEquals(goal("p0"), reduced.put(goal("p0")), "the chain is left unsolved");
        assertEquals(400, reduced.rules().stream().filter(each -> each.rel() == Rel.EQ).count(),
                "and its equalities stay rules");
    }

    @Test
    void aChainWithinTheBoundIsSolved() {
        ReducedRules<String> reduced = ReducedRules.of(new ArrayList<>(chain(20)), ORDER);

        assertNotNull(reduced);
        assertEquals(List.of(), reduced.rules());
    }

    @Test
    void aSetThatContradictsItselfIsLeftAsItWasAndTheOthersAreSolved() {
        List<AffineConstraint<String>> rules = List.of(
                equality(weighing("u", 1, "c", -1, "d", -1), 0),
                equality(weighing("u", 1, "c", -1, "d", -1), 1),
                SMALL);

        ReducedRules<String> reduced = ReducedRules.of(rules, ORDER);

        assertNotNull(reduced);
        assertEquals(Map.of("a", ExactRatio.ONE, "b", ExactRatio.ONE),
                reduced.put(goal("x")).coefs());
        assertEquals(goal("u"), reduced.put(goal("u")));
        assertEquals(2, reduced.rules().size(), "the two that contradict stay rules");
    }

    @Test
    void whereNoSetCanBeSolvedThereIsNothingToLeaveFree() {
        assertNull(ReducedRules.of(List.of(
                equality(weighing("u", 1, "c", -1, "d", -1), 0),
                equality(weighing("u", 1, "c", -1, "d", -1), 1)), ORDER));
    }
}
