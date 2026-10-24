package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * An ordering of one number that every {@code Int} meets narrows no row, and one that the least or
 * the greatest {@code Int} fails does. {@code x < greatest} fails at the greatest, and
 * {@code x <= greatest} does not; a weight below nought turns the ordering, so
 * {@code -x <= -greatest} is {@code x >= greatest}, which the least fails.
 */
class AnOrderingHeldAtBothEndsOfTheIntsNarrowsNothingTest {

    private static final NumericTerm X = new NumericTerm.ValueOf(TermPath.of("x"));
    private static final BigInteger GREATEST = BigInteger.valueOf(Long.MAX_VALUE);
    private static final BigInteger LEAST = BigInteger.valueOf(Long.MIN_VALUE);

    /** {@code weight * x + constant rel 0}. */
    private static boolean vacuous(long weight, BigInteger constant, Rel rel) {
        return DemandReading.endsOfTheInts(new TakenConstraint.Affine(
                new LinearForm<>(ExactRatio.of(constant),
                        Map.of(X, ExactRatio.of(BigInteger.valueOf(weight)))), rel));
    }

    @Test
    void anUpperBoundIsVacuousAtTheGreatestAndAboveItAndNotJustBelowIt() {
        assertEquals(true, vacuous(1, GREATEST.negate(), Rel.LE));
        assertEquals(false, vacuous(1, GREATEST.negate(), Rel.LT));
        assertEquals(true, vacuous(1, GREATEST.negate().subtract(BigInteger.ONE), Rel.LT));
        assertEquals(false, vacuous(1, GREATEST.negate().add(BigInteger.ONE), Rel.LE));
    }

    @Test
    void aLowerBoundIsVacuousAtTheLeastAndBelowItAndNotJustAboveIt() {
        assertEquals(true, vacuous(1, LEAST.negate(), Rel.GE));
        assertEquals(false, vacuous(1, LEAST.negate(), Rel.GT));
        assertEquals(true, vacuous(1, LEAST.negate().add(BigInteger.ONE), Rel.GT));
        assertEquals(false, vacuous(1, LEAST.negate().subtract(BigInteger.ONE), Rel.GE));
    }

    @Test
    void aWeightBelowNoughtTurnsTheOrdering() {
        // -x + greatest >= 0 is x <= greatest, which every Int meets.
        assertEquals(true, vacuous(-1, GREATEST, Rel.GE));
        // -x - greatest <= 0 is x >= -greatest, which the least fails.
        assertEquals(false, vacuous(-1, GREATEST.negate(), Rel.LE));
        // -x + greatest <= 0 is x >= greatest: not vacuous.
        assertEquals(false, vacuous(-1, GREATEST, Rel.LE));
    }

    @Test
    void anEqualityOrADisequalityIsNeverTakenForVacuous() {
        assertEquals(false, vacuous(1, BigInteger.ZERO, Rel.EQ));
        assertEquals(false, vacuous(1, GREATEST.negate().subtract(BigInteger.TEN), Rel.NE));
    }
}
