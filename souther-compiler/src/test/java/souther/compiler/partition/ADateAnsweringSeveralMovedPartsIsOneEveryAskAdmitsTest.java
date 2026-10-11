package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.Place;
import souther.compiler.semantics.TakenAs.DatePart;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A date answering several parts of itself, each taken after it was moved as its own ask says, is
 * one every ask admits, and there is one wherever any date is.
 *
 * <p>The searched-for date is looked for among a decade of days and compared with a walk over every
 * one of them, so what is held is both halves of what a writer of such a date owes: what it offers
 * answers every ask, and it offers nothing only where nothing does. The parts are the calendar's
 * own ({@code java.time}), and the moves and the days they are defined at are the ones a chain of
 * {@code Date.addDays} comes to ({@link DateTranslation#thenAddDays}).
 *
 * <p>Years, months and days are asked together and moved or not, since a group is one question
 * about one date whichever parts it is made of.
 */
class ADateAnsweringSeveralMovedPartsIsOneEveryAskAdmitsTest {

    /** The days a walk covers. A year asked for stands within a few years of this, and a move
     *  takes a date by under two of them. */
    private static final long FIRST = LocalDate.of(1997, 1, 1).toEpochDay();
    private static final long LAST = LocalDate.of(2007, 12, 31).toEpochDay();
    private static final long REACH = 400;

    private static final LocalDate[] DATES = everyDayAround();

    private static LocalDate[] everyDayAround() {
        LocalDate[] dates = new LocalDate[(int) (LAST - FIRST + 1 + 2 * REACH)];
        for (int at = 0; at < dates.length; at++) {
            dates[at] = LocalDate.ofEpochDay(FIRST - REACH + at);
        }
        return dates;
    }

    private static int partOn(DatePart part, long day) {
        LocalDate date = DATES[(int) (day - (FIRST - REACH))];
        return switch (part) {
            case YEAR -> date.getYear();
            case MONTH -> date.getMonthValue();
            case DAY -> date.getDayOfMonth();
        };
    }

    private static final long[] MOVES = {0, 1, -1, 30, -30, 365, -366};

    /** What a chain of moves is defined at, for the chains this walks: defined everywhere, or only
     *  between two days a step of the chain left. */
    private static DateTranslation chain(Random random) {
        long offset = MOVES[random.nextInt(MOVES.length)];
        DateTranslation whole = DateTranslation.none().thenAddDays(offset);
        if (random.nextInt(3) > 0) {
            return whole;
        }
        long from = LocalDate.of(1998 + random.nextInt(9), 1 + random.nextInt(12), 1)
                .toEpochDay();
        return new DateTranslation(offset, from, from + random.nextInt(900));
    }

    private static NumericSet numbers(Random random, DatePart part, boolean lead) {
        int range = switch (part) {
            case YEAR -> 5;
            case MONTH -> 12;
            case DAY -> 31;
        };
        int base = part == DatePart.YEAR ? 2000 : 1;
        Place value = Count.of(base + random.nextInt(range));
        return lead || random.nextBoolean() ? new NumericSet.At(value)
                : new NumericSet.AwayFrom(List.of(value, Count.of(base + random.nextInt(range))));
    }

    private static boolean admits(TermRealizations.DatePartAsk ask, long day) {
        return ask.moved().definedAt(day)
                && ask.wanted().holds(Count.of(partOn(ask.part(), day + ask.moved().offsetDays())),
                        Carrier.WHOLE);
    }

    private static TermRealizations.DatePartAsk year(DateTranslation moved, int year) {
        return new TermRealizations.DatePartAsk(DatePart.YEAR, moved,
                new NumericSet.At(Count.of(year)));
    }

    /**
     * Whatever is offered answers every ask, and nothing is offered only where nothing does.
     */
    @Test
    void whatIsOfferedAnswersEveryAskAndNothingIsOfferedOnlyWhereNothingDoes() {
        Random random = new Random(2255);
        int offered = 0;
        int refused = 0;
        for (int round = 0; round < 600; round++) {
            List<TermRealizations.DatePartAsk> asks = new ArrayList<>();
            asks.add(new TermRealizations.DatePartAsk(DatePart.YEAR, chain(random),
                    numbers(random, DatePart.YEAR, true)));
            int more = random.nextInt(3);
            for (int each = 0; each < more; each++) {
                DatePart part = DatePart.values()[random.nextInt(DatePart.values().length)];
                asks.add(new TermRealizations.DatePartAsk(part, chain(random),
                        numbers(random, part, false)));
            }

            TermRealizations.Search found =
                    TermRealizations.dateAnsweringMovedParts(asks, Carrier.DATE);

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
        assertTrue(offered > 50, "only " + offered + " rounds had a date");
        assertTrue(refused > 50, "only " + refused + " rounds had none");
    }

    /** The year before a move is the one the date is in, and the one after it is the next day's. */
    @Test
    void theFirstDayOfAYearOnAMovedDateIsTheDayBeforeItsFirstOfJanuary() {
        TermRealizations.Search found = TermRealizations.dateAnsweringMovedParts(
                List.of(year(DateTranslation.none().thenAddDays(1), 2027)), Carrier.DATE);

        assertEquals(LocalDate.of(2026, 12, 31), found.on());
    }

    /** Two moves of one date answer two different years only at the first day of the later one. */
    @Test
    void aDateWhoseYearIsOneAndWhoseYesterdaysIsAnotherIsTheFirstOfJanuary() {
        TermRealizations.Search found = TermRealizations.dateAnsweringMovedParts(List.of(
                year(DateTranslation.none(), 2000),
                year(DateTranslation.none().thenAddDays(-1), 1999)), Carrier.DATE);

        assertEquals(LocalDate.of(2000, 1, 1), found.on());
    }

    /**
     * The year of a moved date and the month of the date itself are asked of one date, and neither
     * leaves the other unsolved.
     */
    @Test
    void aMovedYearAndAMonthOfTheDateItselfAreAskedTogether() {
        TermRealizations.Search found = TermRealizations.dateAnsweringMovedParts(List.of(
                year(DateTranslation.none().thenAddDays(-1), 2026),
                new TermRealizations.DatePartAsk(DatePart.MONTH, DateTranslation.none(),
                        new NumericSet.At(Count.of(1)))), Carrier.DATE);

        // Moved a day back it is in 2026, and it is in January: every date from the second of
        // January to the first of February answers both, and the first of them is offered.
        assertEquals(LocalDate.of(2026, 1, 2), found.on());
    }

    /** A day of the month asked beside a moved year is met at the day and not only at a cut. */
    @Test
    void aDayOfTheMonthAskedBesideAMovedYearIsMet() {
        TermRealizations.Search found = TermRealizations.dateAnsweringMovedParts(List.of(
                year(DateTranslation.none().thenAddDays(-1), 2026),
                new TermRealizations.DatePartAsk(DatePart.DAY, DateTranslation.none(),
                        new NumericSet.At(Count.of(17)))), Carrier.DATE);

        assertEquals(LocalDate.of(2026, 1, 17), found.on());
    }

    /** A shift of centuries is as exact as one of a day. */
    @Test
    void aMoveOfCenturiesIsAsExactAsAMoveOfADay() {
        for (long days : new long[] {100_000, -100_000, 36_524_219, -36_524_219}) {
            TermRealizations.Search found = TermRealizations.dateAnsweringMovedParts(
                    List.of(year(DateTranslation.none().thenAddDays(days), 2010)),
                    Carrier.DATE);

            assertEquals(LocalDate.of(2010, 1, 1).minusDays(days), found.on(),
                    "moved by " + days);
        }
    }

    /** A leap year does not move the line: a move of 365 days is not a move of a year. */
    @Test
    void aMoveOfAYearsDaysAcrossALeapDayIsNotAMoveOfAYear() {
        TermRealizations.Search found = TermRealizations.dateAnsweringMovedParts(
                List.of(year(DateTranslation.none().thenAddDays(365), 2025)), Carrier.DATE);

        assertEquals(LocalDate.of(2024, 1, 2), found.on());
    }
}
