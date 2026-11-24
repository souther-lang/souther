package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two equalities, or two disequalities, are one rule where they are the same sum held at the same
 * value or the negated sum held at the negated value, and the answer does not turn on which of the
 * two comparisons is made first.
 *
 * <p>Enumerated at random over sums of two positions with weights from a small set, so the pairs
 * that are equal, equal reversed, and unequal all occur, and each is held to the definition
 * written out here.
 */
class AHeldValueIsEqualToItsReversalWhicheverFieldIsAskedFirstTest {

    private static final long[] WEIGHTS = {-2, -1, 0, 1, 2};
    private static final long[] VALUES = {-3, 0, 3};

    private static CanonicalForm<String> sum(Random random) {
        Map<String, ExactRatio> coefs = new LinkedHashMap<>();
        for (String atom : new String[] {"a", "b"}) {
            long weight = WEIGHTS[random.nextInt(WEIGHTS.length)];
            if (weight != 0) {
                coefs.put(atom, ExactRatio.of(weight));
            }
        }
        if (coefs.isEmpty()) {
            coefs.put("a", ExactRatio.ONE);
        }
        return new CanonicalForm<>(coefs);
    }

    /** The definition: one way round or the other. */
    private static boolean oneRule(CanonicalForm<String> one, ExactRatio at,
                                   CanonicalForm<String> other, ExactRatio there) {
        return (one.equals(other) && at.equals(there))
                || (one.equals(other.negated()) && at.equals(there.negated()));
    }

    /** Equal as the definition says whichever of the two is asked, and hashed alike where equal. */
    private static void askedBothWaysRound(boolean expected, AffineConstraint<String> first,
                                            AffineConstraint<String> second) {
        assertEquals(expected, first.equals(second));
        assertEquals(expected, second.equals(first));
        if (expected) {
            assertEquals(first.hashCode(), second.hashCode());
        }
    }

    @Test
    void anEqualityAndADisequalityAreEqualExactlyWhereTheDefinitionSays() {
        Random random = new Random(2705);
        int same = 0;
        int reversed = 0;
        int apart = 0;
        for (int i = 0; i < 20000; i++) {
            CanonicalForm<String> one = sum(random);
            CanonicalForm<String> other = random.nextInt(3) == 0 ? one
                    : random.nextInt(2) == 0 ? one.negated() : sum(random);
            ExactRatio at = ExactRatio.of(VALUES[random.nextInt(VALUES.length)]);
            ExactRatio there = random.nextBoolean() ? at : at.negated();
            boolean expected = oneRule(one, at, other, there);
            askedBothWaysRound(expected, new AffineConstraint.Equality<>(one, at),
                    new AffineConstraint.Equality<>(other, there));
            askedBothWaysRound(expected, new AffineConstraint.Disequality<>(one, at),
                    new AffineConstraint.Disequality<>(other, there));
            if (!expected) {
                apart++;
            } else if (one.equals(other) && at.equals(there)) {
                same++;
            } else {
                reversed++;
            }
        }
        assertTrue(same > 500 && reversed > 500 && apart > 500,
                "all three kinds of pair must occur: " + same + " " + reversed + " " + apart);
    }
}
