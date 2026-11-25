package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A whole number divided by another and rounded down or up, held to what the exact ratio of the two
 * rounds to.
 *
 * <p>The signs are the whole of what can go wrong: {@link BigInteger#divide} rounds towards nought,
 * so a reader that assumed a positive divisor, or a positive dividend, is right on one quarter of
 * the grid and off by one on another. Every pair of signs is on the grid, with a remainder and
 * without one.
 */
class TheFloorAndTheCeilingOfAQuotientAreTheExactRatiosWhateverTheSignsTest {

    @Test
    void eachRoundsTheWayTheExactQuotientRounds() {
        for (long number = -7; number <= 7; number++) {
            for (long by : new long[] {-3, -2, -1, 1, 2, 3}) {
                ExactRatio exactly = ExactRatio.of(number).dividedBy(ExactRatio.of(by)).orNull();
                String asked = number + " / " + by;
                assertEquals(exactly.floor().orNull(),
                        WholeDivision.floorOf(BigInteger.valueOf(number), BigInteger.valueOf(by)),
                        () -> "the floor of " + asked);
                assertEquals(exactly.ceiling().orNull(),
                        WholeDivision.ceilingOf(BigInteger.valueOf(number), BigInteger.valueOf(by)),
                        () -> "the ceiling of " + asked);
            }
        }
    }

    @Test
    void noughtDividesNothing() {
        assertThrows(ArithmeticException.class,
                () -> WholeDivision.floorOf(BigInteger.ONE, BigInteger.ZERO));
        assertThrows(ArithmeticException.class,
                () -> WholeDivision.ceilingOf(BigInteger.ONE, BigInteger.ZERO));
    }
}
