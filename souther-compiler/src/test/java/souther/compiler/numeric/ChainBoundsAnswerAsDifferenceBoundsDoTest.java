package souther.compiler.numeric;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import org.junit.jupiter.api.Test;

/**
 * Rules that bound one coordinate or the difference of two neighbours are closed by
 * {@link ChainBounds} to the answers {@link DifferenceBounds} gives for the same rules.
 */
class ChainBoundsAnswerAsDifferenceBoundsDoTest {

    private static final CanonicalOrder<Integer> BY_PLACE = Integer::compare;

    private static AffineConstraint<Integer> rule(Map<Integer, Long> weights, long bound,
                                                  boolean inclusive) {
        Map<Integer, ExactRatio> coefs = new LinkedHashMap<>();
        weights.forEach((at, weight) -> coefs.put(at, ExactRatio.of(weight)));
        CanonicalForm.Scaled<Integer> scaled = (CanonicalForm.Scaled<Integer>) CanonicalForm.of(coefs);
        return new AffineConstraint.HalfSpace<>(scaled.form(),
                new ExactCut(ExactRatio.of(bound), inclusive));
    }

    private static List<AffineConstraint<Integer>> randomRules(Random random, int size) {
        List<AffineConstraint<Integer>> rules = new ArrayList<>();
        int count = random.nextInt(size * 3) + 1;
        for (int each = 0; each < count; each++) {
            long bound = random.nextInt(21) - 6L;
            boolean inclusive = random.nextInt(4) != 0;
            int at = random.nextInt(size);
            switch (random.nextInt(4)) {
                case 0 -> rules.add(rule(Map.of(at, 1L), bound, inclusive));
                case 1 -> rules.add(rule(Map.of(at, -1L), bound, inclusive));
                default -> {
                    if (size > 1) {
                        int next = at + 1 < size ? at + 1 : at - 1;
                        Map<Integer, Long> weights = new LinkedHashMap<>();
                        weights.put(at, 1L);
                        weights.put(next, -1L);
                        rules.add(rule(weights, bound, inclusive));
                    }
                }
            }
        }
        return rules;
    }

    @Test
    void everyAnswerIsTheOneTheDifferenceClosureGives() {
        Random random = new Random(3167);
        int compared = 0;
        for (int round = 0; round < 3000; round++) {
            int size = random.nextInt(7) + 1;
            List<AffineConstraint<Integer>> rules = randomRules(random, size);
            ChainBounds chain = ChainBounds.over(rules);
            DifferenceBounds<Integer> dense = DifferenceBounds.over(rules, BY_PLACE);
            assertNotNull(chain);
            assertEquals(dense.holdsNothing(), chain.holdsNothing(), rules.toString());
            assertEquals(dense.everyHopWasComposed(), chain.everyHopWasComposed());
            if (dense.holdsNothing()) {
                continue;
            }
            for (int a = 0; a < size; a++) {
                assertEquals(dense.upperBoundOf(a), chain.upperBoundOf(a), rules + " above " + a);
                assertEquals(dense.lowerBoundOf(a), chain.lowerBoundOf(a), rules + " below " + a);
                for (int b = 0; b < size; b++) {
                    assertEquals(dense.differenceBound(a, b), chain.differenceBound(a, b),
                            rules + " " + a + "-" + b);
                    assertEquals(dense.differenceBoundWasComposed(a, b),
                            chain.differenceBoundWasComposed(a, b));
                    compared++;
                }
            }
        }
        assertEquals(true, compared > 5000);
    }

    @Test
    void aRuleBetweenCoordinatesThatAreNotNeighboursIsLeftToTheDifferenceClosure() {
        Map<Integer, Long> weights = new LinkedHashMap<>();
        weights.put(0, 1L);
        weights.put(2, -1L);
        assertNull(ChainBounds.over(List.of(rule(weights, 3, true))));
    }
}
