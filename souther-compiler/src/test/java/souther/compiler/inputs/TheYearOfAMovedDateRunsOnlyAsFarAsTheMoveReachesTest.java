package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
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
 */
class TheYearOfAMovedDateRunsOnlyAsFarAsTheMoveReachesTest {

    private static final Symbols SYMBOLS = Symbols.none(DefaultStdlib.get());
    private static final TermPath AT = TermPath.of("b");
    private static final ValueName.Stdlib YEAR = ValueName.Stdlib.operation("Date", "year");

    private static NumericTerm.TakenOf yearOf(ValueTransformation from) {
        NumericTerm.TakenOf made = NumericTerm.TakenOf.of(YEAR,
                new ObservationSource(AT, from), TakenArguments.NONE, Type.Prim.DATE,
                souther.compiler.check.ScopedDeclarations.wrapsOf(SYMBOLS), SYMBOLS);
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

    private static NumericDomain.Bounds years(int least, int most) {
        return new NumericDomain.Bounds(Endpoint.inclusive(Count.of(least)),
                Endpoint.inclusive(Count.of(most)));
    }

    @Test
    void theYearOfADateRunsAsFarAsTheCalendar() {
        assertEquals(years(LocalDate.MIN.getYear(), LocalDate.MAX.getYear()),
                yearOf(ValueTransformation.NONE).intrinsicBounds());
    }

    /** Moved a day on, the last date is the one before the last, and a year of the first is
     *  still the first. */
    @Test
    void aMoveForwardReachesFromTheFirstYearToTheLastDatesYear() {
        assertEquals(years(LocalDate.MIN.plusDays(1).getYear(), LocalDate.MAX.getYear()),
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

        assertEquals(years(undone.firstMoved().getYear(), undone.lastMoved().getYear()), bounds);
    }
}
