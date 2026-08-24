package souther.compiler.check;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.semantics.ConstantArguments;
import souther.compiler.semantics.ResultRange;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.time.LocalDate;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Two of the declared bounds are not about the operation alone: the year of a date and a count of
 * minutes between two date-times stop where the calendar the values are written in stops. What a
 * value of the type can be is the carrier's answer ({@link Carrier#extent}), so the declaration and
 * the carrier are two projections of one universe of temporal values, and a day the one holds that
 * the other's year is outside would be a value nothing could be read at.
 *
 * <p>Held here and not where they are declared. The declarations are below this check and cannot see
 * a carrier; and the carrier reads the counts a value is on while a fact reads what an operation
 * answers of it, so neither is the other's to state. What they share is {@code java.time}, and this
 * is where both can be asked.
 */
class ADeclaredBoundIsWhereTheCarrierStopsTest {

    private static NumericDomain.Bounds declaredFor(String module, String operation) {
        return ResultRange.of(ValueName.Stdlib.operation(module, operation), ConstantArguments.NONE);
    }

    /** The count an end of a carrier's extent is at, which is where the values of that carrier
     *  stop. */
    private static BigDecimal endOf(Carrier carrier, boolean lower) {
        Endpoint end = lower ? carrier.extent().low() : carrier.extent().high();
        return Count.number(end.at()).at();
    }

    /**
     * A date's year, against the day counts a date runs between. Read through {@code LocalDate}
     * both times, which is what makes this a comparison of two readings of one universe rather than
     * of two numbers that were written down.
     */
    @Test
    void theYearOfADateStopsWhereADateDoes() {
        NumericDomain.Bounds declared = declaredFor("Date", "year");
        long first = LocalDate.ofEpochDay(endOf(new Carrier.Days(), true).longValueExact()).getYear();
        long last = LocalDate.ofEpochDay(endOf(new Carrier.Days(), false).longValueExact()).getYear();
        assertEquals(new NumericDomain.Bounds(Endpoint.inclusive(Count.of(first)),
                        Endpoint.inclusive(Count.of(last))), declared,
                "the years a date can be written in are the years of the first date and the last");
    }

    /**
     * And the minutes between two date-times, against the seconds a date-time runs between. No two
     * of them stand further apart than the first and the last, either way round.
     */
    @Test
    void aCountOfMinutesStopsWhereTwoDateTimesStopStandingApart() {
        NumericDomain.Bounds declared = declaredFor("DateTime", "minutesBetween");
        BigDecimal apart = endOf(new Carrier.Seconds(), false)
                .subtract(endOf(new Carrier.Seconds(), true))
                .divideToIntegralValue(BigDecimal.valueOf(60));
        assertEquals(new NumericDomain.Bounds(Endpoint.inclusive(Count.of(apart.negate())),
                        Endpoint.inclusive(Count.of(apart))), declared,
                "a count of minutes reaches as far as the first date-time and the last stand apart");
    }
}
