package souther.compiler.numeric;

import org.junit.jupiter.api.Test;
import souther.compiler.numeric.AffineConstraint.Read;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Nought is the one node every bounded position has an edge to or from, so a record of pairs, each
 * bounded and each related only to its own other half, closes over every two of them once it has
 * gone through nought. Gone through last, that is one pass; gone through first, every position gone
 * through after it composes every row, and the closure costs the cube of how many positions there
 * are.
 *
 * <p>Held as a count of the hops composed, over doublings, and beside it what the closure answers,
 * which does not turn on the order.
 */
class NoughtIsGoneThroughOnceWhenTheDifferencesCloseTest {

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
    void doublingThePairsAboutQuadruplesTheHops() {
        Map<Integer, Long> hops = new LinkedHashMap<>();
        for (int pairs : new int[] {20, 40, 80}) {
            hops.put(pairs, hopsOver(pairs));
        }
        assertTrue(hops.get(40) <= hops.get(20) * 5, "40 pairs: " + hops);
        assertTrue(hops.get(80) <= hops.get(40) * 5, "80 pairs: " + hops);
    }

    @Test
    void andWhatItClosesToIsEveryBoundThroughNought() {
        DifferenceBounds<String> closed =
                DifferenceBounds.over(pairs(3), CanonicalOrder.asTheyAreSpelled());
        assertEquals(ExactCut.inclusive(ExactRatio.of(100)), closed.upperBoundOf("a0"));
        assertEquals(ExactCut.inclusive(ExactRatio.of(100)), closed.differenceBound("b0", "a1"));
        assertEquals(ExactCut.inclusive(ExactRatio.of(0)), closed.differenceBound("a2", "b2"));
    }
}
