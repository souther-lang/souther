package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.Place;
import souther.compiler.semantics.TakenAs.DatePart;
import souther.test.Nightly;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A date answering several parts of itself, each moved as an ask drawn at random says, is one every
 * ask admits, and there is one wherever any date is.
 *
 * <p>The claims are {@code ADateAnsweringSeveralMovedPartsIsOneEveryAskAdmitsTest}'s first two, held
 * against the same walks over every day: what is offered answers every ask and nothing is offered
 * only where nothing does, among a decade of days, and for months and days with no year among them,
 * over more than a cycle. The cases there are each answered on one day, a day the search reaches only
 * through one kind of cut. What this adds is the combinations: up to three asks drawn together, each
 * moved by a day, a month's days or a year's days either way or not at all, each defined everywhere
 * or only from the first of a drawn month for a drawn number of days, each wanting a value or leaving
 * out two — days of the month left out among them, three narrowed asks overlapping, and narrowed
 * asks that cross the end of a year, which no written case puts together. The seeds are fixed, so a
 * round that fails is the same round when it is run again.
 *
 * <p>Nightly, for what it costs: hundreds of searches, each held against a walk over every day of a
 * decade or of a cycle. No cheaper way asks whether a combination the written cases do not name
 * goes wrong, and what it finds is as well found by the morning as by the change that caused it,
 * since the written cases stand in the run every change waits on.
 */
@Nightly
class ADateAnsweringDrawnMovedPartsIsOneEveryAskAdmitsTest {

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

    private static final List<DatePart> PARTS = List.of(DatePart.values());

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
                DatePart part = PARTS.get(random.nextInt(PARTS.size()));
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

    /** The first day a walk of one cycle starts at, where the asks are defined there. */
    private static final long CYCLE_FROM = LocalDate.of(2000, 1, 1).toEpochDay();

    /** The days of one Gregorian cycle, counted with {@code java.time}. */
    private static final long CYCLE = LocalDate.of(2400, 1, 1).toEpochDay() - CYCLE_FROM;

    /** The month and the day of every date from a little before the cycle to a little after it,
     *  so a walk over all of them reads an array rather than the calendar. */
    private static final long WIDE_FROM = CYCLE_FROM - 4 * REACH;
    private static final int[] MONTHS = new int[(int) (CYCLE + 8 * REACH)];
    private static final int[] DAYS = new int[MONTHS.length];

    static {
        for (int at = 0; at < MONTHS.length; at++) {
            LocalDate date = LocalDate.ofEpochDay(WIDE_FROM + at);
            MONTHS[at] = date.getMonthValue();
            DAYS[at] = date.getDayOfMonth();
        }
    }

    private static boolean admitsWide(TermRealizations.DatePartAsk ask, long day) {
        if (!ask.moved().definedAt(day)) {
            return false;
        }
        int at = (int) (day + ask.moved().offsetDays() - WIDE_FROM);
        int value = ask.part() == DatePart.MONTH ? MONTHS[at] : DAYS[at];
        return ask.wanted().holds(Count.of(value), Carrier.WHOLE);
    }

    /**
     * Months and days with no year among them are answered by a date every ask admits, and nothing
     * is offered only where no date does.
     *
     * <p>Held against a walk over every day of more than a cycle around where the search starts,
     * which covers every day the narrower moves here are defined at. The walk knows nothing of
     * where the search starts or stops, so neither the window it picks nor the cuts it makes can
     * leave a date out unseen.
     */
    @Test
    void monthsAndDaysWithNoYearAreAnsweredWhereverADateAnswersThem() {
        Random random = new Random(2443);
        List<DatePart> noYear = List.of(DatePart.MONTH, DatePart.DAY);
        int offered = 0;
        int refused = 0;
        for (int round = 0; round < 300; round++) {
            List<TermRealizations.DatePartAsk> asks = new ArrayList<>();
            int many = 1 + random.nextInt(3);
            for (int each = 0; each < many; each++) {
                DatePart part = noYear.get(random.nextInt(noYear.size()));
                asks.add(new TermRealizations.DatePartAsk(part, chain(random),
                        numbers(random, part, random.nextBoolean())));
            }
            boolean somethingAnswers = false;
            for (long day = WIDE_FROM + REACH; day < WIDE_FROM + MONTHS.length - REACH
                    && !somethingAnswers; day++) {
                somethingAnswers = true;
                for (TermRealizations.DatePartAsk ask : asks) {
                    if (!admitsWide(ask, day)) {
                        somethingAnswers = false;
                        break;
                    }
                }
            }

            TermRealizations.Search found =
                    TermRealizations.dateAnsweringMovedParts(asks, Carrier.DATE);

            String where = asks.toString();
            assertTrue(found.everyOne(), "a cycle is every day there is to ask: " + where);
            assertEquals(somethingAnswers, found.on() != null, where);
            if (found.on() == null) {
                refused++;
            } else {
                long day = found.on().toEpochDay();
                assertTrue(asks.stream().allMatch(ask -> admitsWide(ask, day)),
                        found.on() + " was offered and does not answer every ask: " + where);
                offered++;
            }
        }
        assertTrue(offered > 50, "only " + offered + " rounds had a date");
        assertTrue(refused > 20, "only " + refused + " rounds had none");
    }
}
