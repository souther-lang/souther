package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.partition.ContainersAddingUp.Ends;
import souther.compiler.partition.ContainersAddingUp.Split;
import souther.compiler.partition.ContainersAddingUp.Spread;

import java.math.BigDecimal;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A level share on a dense order is rounded to the most places the numbers taking part in the
 * sharing were written to: the total, the start every element moves from, and an end only once a
 * share has been moved to it.
 *
 * <p>Both halves are about places a number was written to, which an exact ratio does not hold —
 * {@code 0.00} and {@code 0} are one ratio. So each case here is one where the number is the same
 * and only its places differ, and the shares tell the two apart.
 */
class ALevelShareIsRoundedToThePlacesItsOwnNumbersWereWrittenToTest {

    private static final Carrier DENSE = new Carrier.Dense();

    /**
     * A start written to two places shares a total written to one out to two, taken through
     * {@link Ends#of} so the start is the count the rules name rather than one this test built.
     */
    @Test
    void aStartWrittenToTwoPlacesSharesToTwoPlaces() {
        NumericDomain.Bounds runs = new NumericDomain.Bounds(
                Endpoint.inclusive(Count.of(new BigDecimal("0.00"))), null);

        assertEquals(List.of(new BigDecimal("0.36"), new BigDecimal("0.37"), new BigDecimal("0.37")),
                level(new BigDecimal("1.1"), 3, Ends.of(runs, DENSE)),
                "the start is one of the numbers every share is worked out from, so its two places"
                        + " are the sharing's even where the total was written to one");
    }

    /** The same start written without places leaves the sharing at the total's one. */
    @Test
    void theSameStartWrittenWithoutPlacesSharesToTheTotals() {
        NumericDomain.Bounds runs = new NumericDomain.Bounds(
                Endpoint.inclusive(Count.of(BigDecimal.ZERO)), null);

        assertEquals(List.of(new BigDecimal("0.3"), new BigDecimal("0.4"), new BigDecimal("0.4")),
                level(new BigDecimal("1.1"), 3, Ends.of(runs, DENSE)),
                "nought written as nought adds no places, so the total's one is all there are");
    }

    /**
     * An end no share is moved to takes no part in the sharing, however many places it was written
     * to.
     */
    @Test
    void anEndNoShareReachesAddsNoPlaces() {
        Ends ends = new Ends(Count.ZERO, null, Count.of(new BigDecimal("1.234")),
                NumericDomain.Bounds.OPEN);

        assertEquals(List.of(new BigDecimal("0.3"), new BigDecimal("0.4"), new BigDecimal("0.4")),
                level(new BigDecimal("1.1"), 3, ends),
                "every share stays short of 1.234, so its three places are not the sharing's");
    }

    private static List<BigDecimal> level(BigDecimal total, int many, Ends ends) {
        Split split = ContainersAddingUp.splitting(total, many, ends, Spread.LEVEL, DENSE);
        return assertInstanceOf(Split.Some.class, split,
                "three shares of " + total + " from " + ends.from() + " decompose").values();
    }
}
