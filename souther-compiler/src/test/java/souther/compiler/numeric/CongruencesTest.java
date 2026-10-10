package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Two classes of whole numbers have in common exactly what stepping through them finds.
 *
 * <p>Held against that stepping over every pair of small divisors and residues, the ones that share
 * a factor included: those are where a solution turns on the difference of the residues and not on
 * the divisors alone.
 */
class CongruencesTest {

    private static BigInteger n(long value) {
        return BigInteger.valueOf(value);
    }

    @Test
    void theMeetOfTwoClassesIsTheNumbersBothHold() {
        for (int one = 1; one <= 12; one++) {
            for (int other = 1; other <= 12; other++) {
                for (int a = 0; a < one; a++) {
                    for (int b = 0; b < other; b++) {
                        Congruences met = new Congruences(n(a), n(one))
                                .meet(new Congruences(n(b), n(other)));
                        for (int x = -200; x <= 200; x++) {
                            boolean both = Math.floorMod(x, one) == a && Math.floorMod(x, other) == b;
                            boolean held = met != null
                                    && met.residue().equals(n(Math.floorMod(x, met.modulus().intValue())));
                            assertEquals(both, held, x + " in " + a + " mod " + one + " and "
                                    + b + " mod " + other);
                        }
                    }
                }
            }
        }
    }

    @Test
    void twoClassesWhoseResiduesDifferByWhatTheirCommonFactorDoesNotDivideShareNothing() {
        assertNull(new Congruences(n(0), n(4)).meet(new Congruences(n(1), n(6))));
    }

    @Test
    void theNumberNearestAnEndIsFoundByArithmetic() {
        Congruences class7 = new Congruences(n(3), n(7));
        assertEquals(n(10), class7.leastAtOrAbove(n(4)));
        assertEquals(n(10), class7.leastAtOrAbove(n(10)));
        assertEquals(n(-4), class7.leastAtOrAbove(n(-4)));
        assertEquals(n(3), class7.greatestAtOrBelow(n(9)));
        assertEquals(n(-4), class7.greatestAtOrBelow(n(-1)));
    }

    @Test
    void largeDivisorsAreNotSteppedThrough() {
        Congruences met = new Congruences(n(3), n(1_000_003))
                .meet(new Congruences(n(4), n(1_000_033)));
        assertEquals(n(1_000_003L * 1_000_033L), met.modulus());
        assertEquals(n(3), met.residue().mod(n(1_000_003)));
        assertEquals(n(4), met.residue().mod(n(1_000_033)));
    }
}
