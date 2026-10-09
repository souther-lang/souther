package souther.runtime;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A list's sum is one sum of its elements, so whether it is a value does not turn on the order the
 * list holds them in.
 *
 * <p>A fine element and an ordinary one have an exact sum with as many digits as their scales are
 * apart, which no run holds. A list holding the fine element's negation as well sums to the
 * ordinary one, whichever of the three comes first: the two fine ones meet first, and the run
 * never forms the sum it has no room for.
 */
class AListsSumIsOneSumOfItsElementsTest {

    private static final Rational FINE = Rational.of(new BigDecimal(BigInteger.ONE, 1 << 30));

    @Test
    void aFineElementAndItsNegationCancelWhereverTheOrdinaryOneStands() {
        Rational fineNegated = Rational.ZERO.minus(FINE);
        for (List<Rational> order : List.of(List.of(FINE, Rational.ONE, fineNegated),
                List.of(Rational.ONE, FINE, fineNegated),
                List.of(FINE, fineNegated, Rational.ONE))) {
            assertEquals(Rational.ONE, Lists.sumRational(order), () -> "in the order " + order);
        }
    }
}
