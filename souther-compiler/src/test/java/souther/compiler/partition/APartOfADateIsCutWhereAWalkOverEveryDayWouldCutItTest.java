package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.DateTranslation;
import souther.compiler.semantics.TakenAs.DatePart;

import java.time.LocalDate;
import java.util.BitSet;
import java.util.Random;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.function.IntPredicate;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A year, a month or a day of the month is cut at the days a walk over every one of the days would
 * cut at, however the set of numbers it leaves is, wherever the range lies, and however far the
 * date was moved.
 *
 * <p>A month and a day are cut by visiting the years or the months of the range, and a year by
 * visiting the years; the expectation here is the walk over the days, read off {@code java.time}
 * and not off the code under test.
 */
class APartOfADateIsCutWhereAWalkOverEveryDayWouldCutItTest {

    private static final long FIRST_DAY = LocalDate.MIN.toEpochDay();
    private static final long LAST_DAY = LocalDate.MAX.toEpochDay();
    private static final long[] OFFSETS = {0, -1, 1, 17, -31, 400};
    private static final int RANGES_A_SET_IS_ASKED_OVER = 40;
    private static final int SETS = 120;

    @Test
    void aDayOfTheMonthIsCutWhereTheWalkOverEveryDayCutsIt() {
        for (int set = 0; set < SETS; set++) {
            BitSet left = tableOf(new Random(3004 + set), set, 31);
            cutsEverywhereAsTheWalkDoes(DatePart.DAY, left::get, set, 900);
        }
    }

    @Test
    void aMonthIsCutWhereTheWalkOverEveryDayCutsIt() {
        for (int set = 0; set < SETS; set++) {
            BitSet left = tableOf(new Random(3005 + set), set, 12);
            cutsEverywhereAsTheWalkDoes(DatePart.MONTH, left::get, set, 3000);
        }
    }

    @Test
    void aYearIsCutWhereTheWalkOverEveryDayCutsIt() {
        for (int set = 0; set < SETS; set++) {
            int modulus = 2 + set % 9;
            int kept = 1 + set % (modulus - 1);
            cutsEverywhereAsTheWalkDoes(DatePart.YEAR, year -> Math.floorMod(year, modulus) < kept,
                    set, 6000);
        }
    }

    /** Some sets leave nearly nothing, some nearly everything, so that the turns are few and many. */
    private static BitSet tableOf(Random random, int set, int most) {
        BitSet left = new BitSet(most + 1);
        double density = set % 3 == 0 ? 0.1 : set % 3 == 1 ? 0.5 : 0.9;
        for (int number = 1; number <= most; number++) {
            left.set(number, random.nextDouble() < density);
        }
        return left;
    }

    private static void cutsEverywhereAsTheWalkDoes(DatePart part, IntPredicate leaves, int set,
            int longest) {
        Random random = new Random(set);
        for (int range = 0; range < RANGES_A_SET_IS_ASKED_OVER; range++) {
            long offset = OFFSETS[random.nextInt(OFFSETS.length)];
            DateTranslation moved = DateTranslation.none().thenAddDays(offset);
            long from = startOf(random, range, moved);
            long to = from + random.nextInt(1, longest);
            if (range % 8 == 7) {
                to = from + random.nextInt(1, 4);
            }
            // A range past where the move is defined is one the cut is still asked over, and its
            // ends read as the calendar's first and last day.
            if (range % 5 != 4) {
                to = Math.min(moved.last(), to);
            }
            assertEquals(walked(part, leaves, moved, from, to), asked(part, leaves, moved, from, to),
                    part + " set " + set + " from " + from + " to " + to + " moved by " + offset);
        }
    }

    /** Ranges that begin at the start, the end and the middle of the calendar, and at month ends. */
    private static long startOf(Random random, int range, DateTranslation moved) {
        return switch (range % 5) {
            case 0 -> moved.first();
            case 1 -> Math.max(moved.first(), moved.last() - random.nextInt(0, 1200));
            case 2 -> LocalDate.of(2000 + random.nextInt(60), 1 + random.nextInt(12), 28)
                    .toEpochDay();
            case 3 -> moved.first() + random.nextInt(0, 1200);
            default -> random.nextBoolean() ? FIRST_DAY - random.nextInt(0, 40)
                    : LAST_DAY - random.nextInt(0, 40);
        };
    }

    private static SortedSet<Long> asked(DatePart part, IntPredicate leaves, DateTranslation moved,
            long from, long to) {
        SortedSet<Long> cuts = new TreeSet<>();
        new TermRealizations.PutToTheDays(
                new TermRealizations.DatePartAsk(part, moved, new NumericSet.At(Count.of(1))),
                leaves, false).cutsInto(cuts, from, to);
        return cuts;
    }

    private static SortedSet<Long> walked(DatePart part, IntPredicate leaves, DateTranslation moved,
            long from, long to) {
        SortedSet<Long> cuts = new TreeSet<>();
        for (long edge : new long[] {moved.first(), moved.last() + 1}) {
            addIfBetween(cuts, edge, from, to);
        }
        long low = Math.max(FIRST_DAY, Math.min(LAST_DAY, from + moved.offsetDays()));
        long high = Math.max(FIRST_DAY, Math.min(LAST_DAY, to + moved.offsetDays()));
        for (long day = low + 1; day <= high; day++) {
            if (leaves.test(numberOn(part, day)) != leaves.test(numberOn(part, day - 1))) {
                addIfBetween(cuts, day - moved.offsetDays(), from, to);
            }
        }
        return cuts;
    }

    private static int numberOn(DatePart part, long day) {
        LocalDate date = LocalDate.ofEpochDay(day);
        return switch (part) {
            case YEAR -> date.getYear();
            case MONTH -> date.getMonthValue();
            case DAY -> date.getDayOfMonth();
        };
    }

    private static void addIfBetween(SortedSet<Long> cuts, long day, long from, long to) {
        if (from < day && day <= to) {
            cuts.add(day);
        }
    }
}
