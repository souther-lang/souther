package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.Place;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A date answering the years of itself moved by several shifts is one every ask admits, and there
 * is one wherever any date is.
 *
 * <p>The searched-for date is looked for among a few centuries of days and compared with a walk
 * over every one of them, so what is held is both halves of what a writer of such a date owes: what
 * it offers answers every ask, and it offers nothing only where nothing does. The years are the
 * calendar's own ({@code java.time}), and the shifts and the days they are defined at are the ones
 * a chain of {@code Date.addDays} comes to ({@link DateTranslation#thenAddDays}).
 */
class ADateAnsweringSeveralShiftedYearsIsOneEveryAskAdmitsTest {

    /** The days a walk covers. A year asked for stands within a few years of this, and a shift
     *  moves a date by under three of them. */
    private static final long FIRST = LocalDate.of(1997, 1, 1).toEpochDay();
    private static final long LAST = LocalDate.of(2007, 12, 31).toEpochDay();
    private static final long REACH = 400;

    private static final int[] YEAR_OF = yearsOfEveryDayAround();

    private static int[] yearsOfEveryDayAround() {
        int[] years = new int[(int) (LAST - FIRST + 1 + 2 * REACH)];
        for (int at = 0; at < years.length; at++) {
            years[at] = LocalDate.ofEpochDay(FIRST - REACH + at).getYear();
        }
        return years;
    }

    private static int yearOn(long day) {
        return YEAR_OF[(int) (day - (FIRST - REACH))];
    }

    private static final long[] SHIFTS = {0, 1, -1, 30, -30, 365, -366};

    /** What a chain of shifts is defined at, for the chains this walks: defined everywhere, or only
     *  between two days a rule of the chain left. */
    private static DateTranslation chain(Random random) {
        long offset = SHIFTS[random.nextInt(SHIFTS.length)];
        DateTranslation whole = DateTranslation.none().thenAddDays(offset);
        if (random.nextInt(3) > 0) {
            return whole;
        }
        long from = LocalDate.of(1998 + random.nextInt(9), 1 + random.nextInt(12), 1)
                .toEpochDay();
        return new DateTranslation(offset, from, from + random.nextInt(900));
    }

    private static NumericSet years(Random random, boolean lead) {
        Place year = Count.of(2000 + random.nextInt(5));
        return lead || random.nextBoolean() ? new NumericSet.At(year)
                : new NumericSet.AwayFrom(List.of(year, Count.of(2000 + random.nextInt(5))));
    }

    private static boolean admits(TermRealizations.ShiftedYear ask, long day) {
        return ask.moved().definedAt(day)
                && ask.wanted().holds(Count.of(yearOn(day + ask.moved().offsetDays())),
                        Carrier.WHOLE);
    }

    /**
     * Whatever is offered answers every ask, and nothing is offered only where no date among those
     * walked answers them.
     */
    @Test
    void whatIsOfferedAnswersEveryAskAndNothingIsOfferedOnlyWhereNothingDoes() {
        Random random = new Random(2255);
        int offered = 0;
        int refused = 0;
        for (int round = 0; round < 400; round++) {
            List<TermRealizations.ShiftedYear> asks = new ArrayList<>();
            int many = 1 + random.nextInt(3);
            for (int each = 0; each < many; each++) {
                asks.add(new TermRealizations.ShiftedYear(chain(random), years(random, each == 0)));
            }

            TermRealizations.Search found =
                    TermRealizations.dateWhoseShiftedYearsAre(asks, Carrier.DATE);

            boolean somethingAnswers = false;
            for (long day = FIRST; day <= LAST && !somethingAnswers; day++) {
                final long on = day;
                somethingAnswers = asks.stream().allMatch(ask -> admits(ask, on));
            }
            String where = asks.toString();
            if (somethingAnswers) {
                assertNotNull(found.on(),
                        "a date answers every ask, and none was offered: " + where);
            }
            if (found.on() == null) {
                assertTrue(found.everyOne(),
                        "nothing was offered by a walk that stopped: " + where);
                assertFalse(somethingAnswers, where);
                refused++;
            } else {
                long day = found.on().toEpochDay();
                assertTrue(asks.stream().allMatch(ask -> admits(ask, day)),
                        found.on() + " was offered and does not answer every ask: " + where);
                offered++;
            }
        }
        // So that a walk which offered nothing, or refused nothing, cannot pass for one that was
        // right every time.
        assertTrue(offered > 20, "only " + offered + " rounds had a date");
        assertTrue(refused > 20, "only " + refused + " rounds had none");
    }

    /** The year before a shift is one the date is in, and the one after it is the next day's. */
    @Test
    void theFirstDayOfAYearOnAShiftedDateIsTheDayBeforeItsFirstOfJanuary() {
        TermRealizations.Search found = TermRealizations.dateWhoseShiftedYearsAre(
                List.of(new TermRealizations.ShiftedYear(DateTranslation.none().thenAddDays(1),
                        new NumericSet.At(Count.of(2027)))), Carrier.DATE);

        assertEquals(LocalDate.of(2026, 12, 31), found.on());
    }

    /** Two shifts of one date answer two different years only at the first day of the later one. */
    @Test
    void aDateWhoseYearIsOneAndWhoseYesterdaysIsAnotherIsTheFirstOfJanuary() {
        TermRealizations.Search found = TermRealizations.dateWhoseShiftedYearsAre(List.of(
                new TermRealizations.ShiftedYear(DateTranslation.none(),
                        new NumericSet.At(Count.of(2000))),
                new TermRealizations.ShiftedYear(DateTranslation.none().thenAddDays(-1),
                        new NumericSet.At(Count.of(1999)))), Carrier.DATE);

        assertEquals(LocalDate.of(2000, 1, 1), found.on());
    }

    /** A shift of centuries of days is as exact as one of a day. */
    @Test
    void aShiftOfCenturiesIsAsExactAsAShiftOfADay() {
        for (long days : new long[] {100_000, -100_000, 36_524_219, -36_524_219}) {
            TermRealizations.Search found = TermRealizations.dateWhoseShiftedYearsAre(
                    List.of(new TermRealizations.ShiftedYear(
                            DateTranslation.none().thenAddDays(days),
                            new NumericSet.At(Count.of(2010)))), Carrier.DATE);

            assertEquals(LocalDate.of(2010, 1, 1).minusDays(days), found.on(),
                    "shifted by " + days);
        }
    }

    /** A leap year does not move the line: a shift of 365 days is not a shift of a year. */
    @Test
    void aShiftOfAYearsDaysAcrossALeapDayIsNotAShiftOfAYear() {
        TermRealizations.Search found = TermRealizations.dateWhoseShiftedYearsAre(
                List.of(new TermRealizations.ShiftedYear(DateTranslation.none().thenAddDays(365),
                        new NumericSet.At(Count.of(2025)))), Carrier.DATE);

        assertEquals(LocalDate.of(2024, 1, 2), found.on());
    }
}
