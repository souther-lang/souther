package souther.compiler.numeric;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import org.junit.jupiter.api.Test;

/**
 * The closure of a chain says it is complete exactly where the closure of every pair says so.
 *
 * <p>{@link DifferenceBounds} tries the sum of every path, so it says the closure is not complete
 * where two bounds that are each held have a sum that is not — which two whole numbers near the end
 * of what the arithmetic holds do, with no bound on either position beside them. A closure along the
 * chain that did not try those sums would say it was complete, and a basis would be taken for rules
 * it is not exact for. So it is made only for bounds no sum of the chain can be too large for.
 */
class AChainClosureIsCompleteWhereTheDifferenceClosureIsTest {

    private static final CanonicalOrder<Integer> BY_PLACE = Integer::compare;

    private static AffineConstraint<Integer> difference(int from, int to, ExactRatio bound) {
        Map<Integer, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(from, ExactRatio.ONE);
        coefs.put(to, ExactRatio.ONE.negated());
        CanonicalForm.Scaled<Integer> scaled = (CanonicalForm.Scaled<Integer>) CanonicalForm.of(coefs);
        return new AffineConstraint.HalfSpace<>(scaled.form(), ExactCut.inclusive(bound));
    }

    /** Two whole numbers, each held, whose sum has no representation. */
    @Test
    void aBoundNearTheEndOfWhatTheArithmeticHoldsIsLeftToTheDifferenceClosure() {
        ExactRatio near = ExactRatio.of(new BigDecimal(BigInteger.ONE, -Integer.MAX_VALUE));
        List<AffineConstraint<Integer>> rules = List.of(difference(0, 1, near),
                difference(1, 2, ExactRatio.ONE));
        assertEquals(false, DifferenceBounds.over(rules, BY_PLACE).everyHopWasComposed(),
                "the difference closure finds the sum it cannot hold");
        assertNull(ChainBounds.over(rules), "and the chain does not take what it would not find");
    }

    private static ExactRatio wholeOfAtMost(Random dice, int bits) {
        BigInteger magnitude = new BigInteger(dice.nextInt(bits + 1), dice);
        return ExactRatio.of(dice.nextBoolean() ? magnitude : magnitude.negate());
    }

    @Test
    void everyBoundTheChainTakesIsOneNoSumOfItsPathsIsTooLargeFor() {
        Random dice = new Random(3210);
        for (int round = 0; round < 500; round++) {
            int size = 3 + dice.nextInt(8);
            List<AffineConstraint<Integer>> rules = new ArrayList<>();
            for (int at = 0; at + 1 < size; at++) {
                ExactRatio bound = wholeOfAtMost(dice, 1000);
                rules.add(dice.nextBoolean() ? difference(at, at + 1, bound)
                        : difference(at + 1, at, bound));
            }
            ChainBounds chain = ChainBounds.over(rules);
            assertNotNull(chain, "a bound of a thousand bits is one the chain takes");
            assertEquals(DifferenceBounds.over(rules, BY_PLACE).everyHopWasComposed(),
                    chain.everyHopWasComposed());
        }
    }

    /** The ends of an {@code Int} are bounds the chain takes: they are in every rule of a chain of
     *  them. */
    @Test
    void theEndsOfAnIntAreBoundsTheChainTakes() {
        assertNotNull(ChainBounds.over(List.of(difference(0, 1, ExactRatio.of(Long.MAX_VALUE)),
                difference(1, 2, ExactRatio.of(Long.MIN_VALUE)))));
    }

    @Test
    void aBoundOfMoreThanAThousandBitsIsLeftToTheDifferenceClosure() {
        ExactRatio past = ExactRatio.of(BigInteger.ONE.shiftLeft(1001));
        assertNull(ChainBounds.over(List.of(difference(0, 1, past))));
    }
}
