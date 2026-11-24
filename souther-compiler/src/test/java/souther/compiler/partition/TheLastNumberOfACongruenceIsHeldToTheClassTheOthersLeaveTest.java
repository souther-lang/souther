package souther.compiler.partition;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.Map;

import org.junit.jupiter.api.Test;

import souther.compiler.check.HeldClass;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Place;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * Once every number of a congruence but one stands, the values of that one the congruence leaves
 * are exactly those of the class it is held to.
 *
 * <p>The oracle is the congruence worked out here at each value: a value the class holds that does
 * not bring the form to the residue, or one that does and the class leaves out, is a difference
 * from it. One of each kind of case the class turns on, and not a grid of them: a divisor of one,
 * a prime one and one with several factors; weights prime to it, sharing each of its factors
 * with it, negative, of the divisor itself and absent; and the others at values the right side
 * is and is not divisible at, over every residue and two turns of the divisor.
 */
class TheLastNumberOfACongruenceIsHeldToTheClassTheOthersLeaveTest {

    private static final NumericTerm.ValueOf X = new NumericTerm.ValueOf(TermPath.of("x"));
    private static final NumericTerm.ValueOf Y = new NumericTerm.ValueOf(TermPath.of("y"));

    @Test
    void theClassIsEveryValueThatBringsTheFormToTheResidue() {
        long[] weights = {1, -3, 4, 6, 12, 0};
        long[] divisors = {1, 7, 12};
        for (long divisor : divisors) {
            for (long wx : weights) {
                for (long wy : new long[] {1, 4}) {
                    for (long constant = -3; constant <= 0; constant += 3) {
                        for (long residue = 0; residue < divisor; residue++) {
                            for (long y = 0; y <= 2; y++) {
                                agrees(wx, wy, constant, divisor, residue, y);
                            }
                        }
                    }
                }
            }
        }
    }

    private static void agrees(long wx, long wy, long constant, long divisor, long residue,
                               long y) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        if (wx != 0) {
            coefs.put(X, ExactRatio.of(wx));
        }
        coefs.put(Y, ExactRatio.of(wy == 0 ? 1 : wy));
        long weightOfY = wy == 0 ? 1 : wy;
        NumericWitness.Congruent congruent = new NumericWitness.Congruent(
                new LinearForm<>(ExactRatio.of(constant), coefs), BigInteger.valueOf(divisor),
                BigInteger.valueOf(residue));
        Map<NumericTerm, Place> standing = Map.of(Y, Count.of(y));
        HeldClass held = congruent.leavesTheLast(X, standing);
        String said = wx + "·x + " + weightOfY + "·" + y + " + " + constant + " ≡ " + residue
                + " (mod " + divisor + ")";
        for (long x = -divisor; x < divisor; x++) {
            boolean meets = Math.floorMod(wx * x + weightOfY * y + constant, divisor) == residue;
            boolean kept = switch (held) {
                case HeldClass.None _ -> true;
                case HeldClass.NoValue _ -> false;
                default -> held.holds(BigInteger.valueOf(x));
            };
            assertEquals(meets, kept, said + " at x = " + x + ", held to " + held);
        }
    }

    /** A number standing at no whole number leaves the last one no value. */
    @Test
    void aNumberAtNoWholeNumberLeavesNoValue() {
        NumericWitness.Congruent congruent = new NumericWitness.Congruent(
                new LinearForm<>(ExactRatio.ZERO, Map.of(X, ExactRatio.ONE, Y, ExactRatio.ONE)),
                BigInteger.TEN, BigInteger.ZERO);
        assertInstanceOf(HeldClass.NoValue.class, congruent.leavesTheLast(X, Map.of()));
    }
}
