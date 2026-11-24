package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An equality is solved for a position whose weights the other positions' can be divided by, and
 * which one that is does not turn on what the positions are called. Where one weight is a power of
 * ten too large for its reciprocal to be held, the equality is solved for the other position
 * whichever of the two is named first, and is not left out under one naming and read under the
 * other.
 */
class AnEqualityIsSolvedForAPositionItsWeightsCanBeHeldAtTest {

    /** A power of ten whose reciprocal's exponent is more than a {@code long} holds. */
    private static final ExactRatio TOO_SMALL_TO_DIVIDE_BY = ExactRatio.tenTo(Long.MIN_VALUE);

    private static AffineConstraint<String> small(String smallWeighted, String other) {
        Map<String, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(smallWeighted, TOO_SMALL_TO_DIVIDE_BY);
        coefs.put(other, ExactRatio.ONE);
        return new AffineConstraint.Equality<>(new CanonicalForm<>(coefs), ExactRatio.ZERO);
    }

    private static void assertRead(String smallWeighted, String other) {
        EqualitySpan<String> span = EqualitySpan.of(List.of(small(smallWeighted, other)),
                CanonicalOrder.asTheyAreSpelled());

        assertNotNull(span, "the equality is read with " + smallWeighted + " the small weight");
        Map<String, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(smallWeighted, TOO_SMALL_TO_DIVIDE_BY);
        coefs.put(other, ExactRatio.ONE);
        EqualitySpan.Residue<String> left =
                span.residue(new CanonicalForm<>(coefs), ExactRatio.ZERO);
        assertNotNull(left);
        assertTrue(left.coefs().isEmpty() && left.constant().isZero(),
                "the equality itself is nothing once it is taken out: " + left);
    }

    /** The work spent finding a position to solve for is the equality's width, whichever position
     *  is tried first, so the budget at which it is read does not turn on the names. */
    @Test
    void theEqualityIsReadAtTheSameBudgetsWhicheverOfTheTwoPositionsIsNamedFirst() {
        for (int budget = 0; budget <= 12; budget++) {
            boolean one = EqualitySpan.of(List.of(small("a", "b")),
                    CanonicalOrder.asTheyAreSpelled(), budget) != null;
            boolean other = EqualitySpan.of(List.of(small("b", "a")),
                    CanonicalOrder.asTheyAreSpelled(), budget) != null;

            assertEquals(one, other, "read at a budget of " + budget + " under one naming only");
        }
    }

    @Test
    void theEqualityIsReadWhicheverOfTheTwoPositionsIsNamedFirst() {
        assertRead("a", "b");
        assertRead("b", "a");
    }
}
