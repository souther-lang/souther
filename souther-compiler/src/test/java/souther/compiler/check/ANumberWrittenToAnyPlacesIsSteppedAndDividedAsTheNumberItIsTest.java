package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.BoundaryDomain;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Dates;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.Towards;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.partition.CutPosition;
import souther.compiler.partition.Level;
import souther.compiler.semantics.Arithmetic;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.time.LocalDate;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A count is the number and not the places it was written to, so a step along an order, a quotient
 * and a date are worked out of the number whatever places it came with.
 *
 * <p>Nought written to two billion places is a whole number a {@code Whole} order holds, and it
 * reaches the order that way from an observation read as a decimal. Every case here was a
 * {@code BigDecimal} call that wrote one operand to the other's places before answering, and so
 * refused a number with an ordinary answer. Each is asked through the reader that owns it rather
 * than through the arithmetic underneath, so a reader that goes back to the decimals turns it red.
 */
class ANumberWrittenToAnyPlacesIsSteppedAndDividedAsTheNumberItIsTest {

    private static final Count NOUGHT_AT_TWO_BILLION_PLACES =
            Count.of(new BigDecimal(BigInteger.ZERO, Integer.MAX_VALUE));

    private static final Carrier WHOLE = new Carrier.Whole();

    @Test
    void aCountTheWholeOrderHoldsIsSteppedFrom() {
        assertEquals(Optional.of(Count.of(1)),
                BoundaryDomain.on(WHOLE).successor(NOUGHT_AT_TWO_BILLION_PLACES),
                "the order holds nought however it was written, and the count after it is one");
        assertEquals(Optional.of(Count.of(-1)),
                BoundaryDomain.on(WHOLE).predecessor(NOUGHT_AT_TWO_BILLION_PLACES),
                "and the count before it is minus one");
    }

    /** A step no count is — a whole number with more digits than the host holds — is absent. */
    @Test
    void aStepNoCountIsIsAbsentRatherThanAnException() {
        assertNull(Count.of(new BigDecimal(BigInteger.ONE, -2_000_000_000)).plus(1),
                "one past ten to the two billionth is a whole number no host holds");
    }

    @Test
    void aDayCountIsReadAsTheDayItIs() {
        assertEquals(LocalDate.EPOCH, Dates.dateAt(NOUGHT_AT_TWO_BILLION_PLACES),
                "nought days from the epoch is the epoch, whatever places the nought had");
        assertThrows(IllegalArgumentException.class,
                () -> Dates.dateAt(Count.of(new BigDecimal("1.5"))),
                "and a count no date is is refused by name, not by a java.math exception");
    }

    @Test
    void aTruncatingQuotientIsTheNumbersAndSaysWhereItHasNone() {
        assertEquals(ExactAnswer.held(BigDecimal.ZERO),
                Arithmetic.ATruncatingQuotient.quotientOf(
                        NOUGHT_AT_TWO_BILLION_PLACES.at(), BigDecimal.valueOf(3)),
                "nought over three is nought");
        assertEquals(ExactAnswer.unheld(UnheldNumber.NO_REPRESENTATION_EXISTS),
                Arithmetic.ATruncatingQuotient.quotientOf(
                        new BigDecimal(BigInteger.valueOf(5), -2_000_000_000), BigDecimal.valueOf(3)),
                "a quotient with more digits than the host holds is said to be one");
    }

    /** A step to just past a line at a negative number of places is ten to that many. */
    @Test
    void justPastALineAtANegativeNumberOfPlacesIsOneStepOfThosePlaces() {
        CutPosition.JustBeyond beyond =
                CutPosition.at(new Level.OnACarrier(new Carrier.Dense(), Count.ZERO))
                        .justBeyond(Towards.ABOVE, -2_000_000_000);
        CutPosition.JustBeyond.At at = assertInstanceOf(CutPosition.JustBeyond.At.class, beyond,
                "nought is on the grid of every scale, so the place past it is one step up");
        assertEquals(0, ((Count) at.place()).at()
                        .compareTo(new BigDecimal(BigInteger.ONE, -2_000_000_000)),
                "and one step at two billion places left of the point is ten to the two billionth");
    }
}
