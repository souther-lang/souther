package souther.compiler.numeric;

import org.junit.jupiter.api.Test;
import souther.compiler.numeric.AffineConstraint.Read;
import souther.compiler.numeric.DifferenceBounds.Apart;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A difference through nought is two positions' own bounds, and every bounded position has an edge
 * to or from nought, so a closure that kept nought as a node would relate every two of them: a
 * record of many bounded fields would close in the square of how many there were, and a box carried
 * along every relation would be carried along all of those. What is held is what the rules relate.
 *
 * <p>Held as a count of the hops composed, over doublings; as the relations the closure hands a
 * carry; and beside both what the closure answers about a difference through nought, which it
 * still answers.
 */
class TheDifferencesHoldWhatTheRulesRelateAndNoMoreTest {

    private static AffineConstraint<String> stated(Map<String, ExactRatio> coefs, long constant,
                                                   Rel rel) {
        Read<String> read = AffineConstraint.of(coefs, ExactRatio.of(constant), rel,
                atom -> Granularity.DISCRETE);
        assertInstanceOf(Read.Stated.class, read);
        return ((Read.Stated<String>) read).constraint();
    }

    private static Map<String, ExactRatio> weighing(String a, long x, String b, long y) {
        Map<String, ExactRatio> out = new LinkedHashMap<>();
        out.put(a, ExactRatio.of(x));
        if (b != null) {
            out.put(b, ExactRatio.of(y));
        }
        return out;
    }

    /** {@code a_i >= 0}, {@code b_i <= 100} and {@code a_i <= b_i} for each of {@code pairs}. */
    private static List<AffineConstraint<String>> pairs(int pairs) {
        List<AffineConstraint<String>> out = new ArrayList<>();
        for (int i = 0; i < pairs; i++) {
            out.add(stated(weighing("a" + i, 1, null, 0), 0, Rel.GE));
            out.add(stated(weighing("b" + i, 1, null, 0), -100, Rel.LE));
            out.add(stated(weighing("a" + i, 1, "b" + i, -1), 0, Rel.LE));
        }
        return out;
    }

    private static long hopsOver(int pairs) {
        long[] counting = {0};
        DifferenceBounds.COUNTING_HOPS = counting;
        try {
            DifferenceBounds.over(pairs(pairs), CanonicalOrder.asTheyAreSpelled());
        } finally {
            DifferenceBounds.COUNTING_HOPS = null;
        }
        return counting[0];
    }

    @Test
    void doublingThePairsAboutDoublesTheHops() {
        Map<Integer, Long> hops = new LinkedHashMap<>();
        for (int pairs : new int[] {20, 40, 80}) {
            hops.put(pairs, hopsOver(pairs));
        }
        assertTrue(hops.get(40) <= hops.get(20) * 5 / 2, "40 pairs: " + hops);
        assertTrue(hops.get(80) <= hops.get(40) * 5 / 2, "80 pairs: " + hops);
    }

    @Test
    void theRelationsAreTheOnesTheRulesState() {
        DifferenceBounds<String> closed =
                DifferenceBounds.over(pairs(3), CanonicalOrder.asTheyAreSpelled());
        ExactCut atNought = ExactCut.inclusive(ExactRatio.ZERO);
        assertEquals(Set.of(new Apart<>("a0", "b0", atNought), new Apart<>("a1", "b1", atNought),
                        new Apart<>("a2", "b2", atNought)),
                Set.copyOf(closed.relations()));
    }

    @Test
    void andWhatItAnswersIsEveryBoundThroughNought() {
        DifferenceBounds<String> closed =
                DifferenceBounds.over(pairs(3), CanonicalOrder.asTheyAreSpelled());
        assertEquals(ExactCut.inclusive(ExactRatio.of(100)), closed.upperBoundOf("a0"));
        assertEquals(ExactCut.inclusive(ExactRatio.of(100)), closed.differenceBound("b0", "a1"));
        assertEquals(ExactCut.inclusive(ExactRatio.of(0)), closed.differenceBound("a2", "b2"));
    }
}
