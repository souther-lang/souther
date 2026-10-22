package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.check.ScopedDeclarations;
import souther.compiler.check.Symbols;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.ValueTransformation;
import souther.compiler.semantics.TakenArguments;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.time.LocalDate;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where the numbers of a term run is one answer, and it is the term's: the year of a date moved a
 * year's days back never reaches the last year there is, since no date moved that far back is the
 * last date.
 *
 * <p>What the operation declares of the year of any date is met with what the move leaves of the
 * dates, so everything that asks how far the number runs — a line, a border, a search for a date —
 * is told one range.
 *
 * <p>A month and a day of the month are held the same way where the dates the move reaches leave
 * them a run, and are every one the calendar has where they come round.
 */
class TheYearOfAMovedDateRunsOnlyAsFarAsTheMoveReachesTest {

    private static final Symbols SYMBOLS = Symbols.none(DefaultStdlib.get());
    private static final TermPath AT = TermPath.of("b");
    private static final ValueName.Stdlib YEAR = ValueName.Stdlib.operation("Date", "year");

    private static NumericTerm.TakenOf yearOf(ValueTransformation from) {
        NumericTerm.TakenOf made = NumericTerm.TakenOf.of(YEAR,
                new ObservationSource(AT, from), TakenArguments.NONE, Type.Prim.DATE,
                ScopedDeclarations.wrapsOf(SYMBOLS), SYMBOLS);
        assertNotNull(made, "the year of a moved date is a number of the date it was moved from");
        return made;
    }

    private static ValueTransformation moved(long... days) {
        DateTranslation chain = DateTranslation.none();
        for (long each : days) {
            chain = chain.thenAddDays(each);
        }
        return ValueTransformation.of(chain);
    }

    private static NumericDomain.Bounds between(int least, int most) {
        return new NumericDomain.Bounds(Endpoint.inclusive(Count.of(least)),
                Endpoint.inclusive(Count.of(most)));
    }

    @Test
    void theYearOfADateRunsAsFarAsTheCalendar() {
        assertEquals(between(LocalDate.MIN.getYear(), LocalDate.MAX.getYear()),
                yearOf(ValueTransformation.NONE).intrinsicBounds());
    }

    /** Moved a day on, the last date is the one before the last, and a year of the first is
     *  still the first. */
    @Test
    void aMoveForwardReachesFromTheFirstYearToTheLastDatesYear() {
        assertEquals(between(LocalDate.MIN.plusDays(1).getYear(), LocalDate.MAX.getYear()),
                yearOf(moved(1)).intrinsicBounds());
    }

    /** The case the year-of-the-last-date line is drawn at: a year and a day back from the end. */
    @Test
    void aMoveBackAYearAndADayNeverReachesTheLastYear() {
        NumericDomain.Bounds bounds = yearOf(moved(-366)).intrinsicBounds();

        assertEquals(LocalDate.MAX.minusDays(366).getYear(),
                ((Count) bounds.max().at()).at().intValueExact());
        assertFalse(bounds.admits(Count.of(LocalDate.MAX.getYear())),
                "no date moved back that far is in the last year");
        assertTrue(bounds.admits(Count.of(LocalDate.MAX.getYear() - 1)));
    }

    /** Moved and moved back is defined at one date fewer, and says so of the last year it reaches
     *  where that date was the only one in it. */
    @Test
    void aMoveUndoneRunsOverTheDatesItIsDefinedAt() {
        DateTranslation undone = DateTranslation.none().thenAddDays(1).thenAddDays(-1);
        NumericDomain.Bounds bounds = yearOf(ValueTransformation.of(undone)).intrinsicBounds();

        assertEquals(between(undone.firstMoved().getYear(), undone.lastMoved().getYear()), bounds);
    }

    private static NumericTerm.TakenOf partOf(String part, ValueTransformation from) {
        NumericTerm.TakenOf made = NumericTerm.TakenOf.of(
                ValueName.Stdlib.operation("Date", part), new ObservationSource(AT, from),
                TakenArguments.NONE, Type.Prim.DATE,
                ScopedDeclarations.wrapsOf(SYMBOLS), SYMBOLS);
        assertNotNull(made, "a month or a day of a moved date is a number of the date it was"
                + " moved from");
        return made;
    }

    /** The days a move leaves near the end of the calendar, moved: the last forty of them. */
    private static ValueTransformation toTheLastDays(int many) {
        return moved(LocalDate.MAX.toEpochDay() - LocalDate.MIN.toEpochDay() - (many - 1));
    }

    /**
     * Moved to the last forty days there are, a date falls in November and December of the last
     * year, and on every day of the month: the months are a run, and the days come round.
     */
    @Test
    void theMonthsOfDatesInOneYearAreTheRunOfThem() {
        assertEquals(between(11, 12), partOf("month", toTheLastDays(40)).intrinsicBounds());
        assertEquals(between(1, 31), partOf("day", toTheLastDays(40)).intrinsicBounds());
    }

    /** Moved to the last ten days there are, a date falls in December alone, on its last ten. */
    @Test
    void theDaysOfDatesInOneMonthAreTheRunOfThem() {
        assertEquals(between(12, 12), partOf("month", toTheLastDays(10)).intrinsicBounds());
        assertEquals(between(22, 31), partOf("day", toTheLastDays(10)).intrinsicBounds());
    }

    /**
     * Moved onto the twenty-seventh of February to the second of March of a common year, a date
     * falls on the first to the twenty-eighth: the days come round, and the month they come round
     * in is February, whose last day is the twenty-eighth.
     */
    @Test
    void theDaysOfDatesAcrossTheEndOfAShortMonthRunAsFarAsItsLastDay() {
        ValueTransformation across = ValueTransformation.of(new DateTranslation(1,
                LocalDate.of(2001, 2, 26).toEpochDay(), LocalDate.of(2001, 3, 1).toEpochDay()));

        assertEquals(between(1, 28), partOf("day", across).intrinsicBounds());
        assertEquals(between(2, 3), partOf("month", across).intrinsicBounds());
        assertEquals(between(2001, 2001), partOf("year", across).intrinsicBounds());
    }

    /** Moved a day, a date falls in every month and on every day the calendar has. */
    @Test
    void theMonthsAndDaysOfDatesOverYearsAreEveryOne() {
        assertEquals(between(1, 12), partOf("month", moved(1)).intrinsicBounds());
        assertEquals(between(1, 31), partOf("day", moved(-1)).intrinsicBounds());
    }
}
