package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A domain in which nothing holds stays that way under anything further asserted of it.
 *
 * <p>Asserting is refining, and there is nothing left in a contradicted domain to refine. The bounds
 * of one are gone — what would they be bounds on — so an assertion that derived its answer from the
 * bounds it was handed would come back a domain in which that assertion alone is known, which is a
 * wider domain than the one it was asked to narrow.
 *
 * <p>An equality is where this is reached: it is asserted as two bounds one after the other, and the
 * first of them is what a contradicted equality contradicts. Asked as one bound — a floor, a ceiling
 * — the domain is answered before it is built on and the question never arises, which is why the
 * bounds below are asserted both ways round.
 */
class ADomainHoldingNothingHoldsNothingFurtherTest {

    private static final Map<String, Granularity> COUNTS = Map.of("n", Granularity.DISCRETE);

    private static NumericDomain.LinearForm nMinus(long count) {
        return NumericDomain.LinearForm.atom("n")
                .minus(NumericDomain.LinearForm.constant(BigDecimal.valueOf(count)));
    }

    private static NumericDomain atLeastTwo() {
        return NumericDomain.top().assume(nMinus(2), NumericDomain.Rel.GE, COUNTS);
    }

    @Test
    void aFloorIsWhatItSays() {
        assertFalse(atLeastTwo().isBottom(), "two and up is somewhere to be");
        assertFalse(atLeastTwo().assume(nMinus(2), NumericDomain.Rel.EQ, COUNTS).isBottom(),
                "and two is one of them");
    }

    @Test
    void anEqualityBelowAFloorLeavesNothing() {
        assertTrue(atLeastTwo().assume(nMinus(0), NumericDomain.Rel.EQ, COUNTS).isBottom(),
                "nothing is both at least two and none");
        assertTrue(atLeastTwo().assume(nMinus(1), NumericDomain.Rel.EQ, COUNTS).isBottom());
    }

    @Test
    void aCeilingBelowAFloorLeavesNothing() {
        assertTrue(atLeastTwo().assume(nMinus(1), NumericDomain.Rel.LE, COUNTS).isBottom());
    }

    @Test
    void whatHoldsNothingKeepsHoldingNothing() {
        NumericDomain none = atLeastTwo().assume(nMinus(1), NumericDomain.Rel.LE, COUNTS);
        assertTrue(none.assume(nMinus(0), NumericDomain.Rel.EQ, COUNTS).isBottom());
        assertTrue(none.assume(nMinus(5), NumericDomain.Rel.GE, COUNTS).isBottom());
    }
}
