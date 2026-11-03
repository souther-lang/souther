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

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A day of the month is cut at the days a walk over every one of them would cut at, however the set
 * of day numbers it leaves is, wherever the range lies, and however far the date was moved.
 *
 * <p>The cut is found by visiting the months of the range; the expectation here is the walk over
 * its days, read off {@code java.time} and not off the code under test.
 */
class ADayOfTheMonthIsCutAtTheSameDaysAsAWalkOverEveryDayTest {

    private static final long FIRST_DAY = LocalDate.MIN.toEpochDay();
    private static final long LAST_DAY = LocalDate.MAX.toEpochDay();
    private static final long[] OFFSETS = {0, -1, 1, 17, -31, 400};
    private static final int RANGES_A_SET_IS_ASKED_OVER = 40;
    private static final int SETS = 120;

    @Test
    void everyDayIsCutWhereTheWalkOverEveryDayCutsIt() {
        Random random = new Random(3004);
        for (int set = 0; set < SETS; set++) {
            BitSet left = new BitSet(32);
            // Some sets leave nearly nothing, some nearly everything, so that the turns are few
            // and many.
            double density = set % 3 == 0 ? 0.1 : set % 3 == 1 ? 0.5 : 0.9;
            for (int number = 1; number <= 31; number++) {
                left.set(number, random.nextDouble() < density);
            }
            for (int range = 0; range < RANGES_A_SET_IS_ASKED_OVER; range++) {
                long offset = OFFSETS[random.nextInt(OFFSETS.length)];
                DateTranslation moved = DateTranslation.none().thenAddDays(offset);
                long from = startOf(random, range, moved);
                long to = from + random.nextInt(1, 900);
                if (range % 8 == 7) {
                    to = from + random.nextInt(1, 4);
                }
                // A range past where the move is defined is one the cut is still asked over, and
                // its ends read as the calendar's first and last day.
                if (range % 5 != 4) {
                    to = Math.min(moved.last(), to);
                }
                assertEquals(walked(left, moved, from, to), asked(left, moved, from, to),
                        "set " + left + " from " + from + " to " + to + " moved by " + offset);
            }
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

    private static SortedSet<Long> asked(BitSet left, DateTranslation moved, long from, long to) {
        SortedSet<Long> cuts = new TreeSet<>();
        new TermRealizations.PutToTheDays(
                new TermRealizations.DatePartAsk(DatePart.DAY, moved,
                        new NumericSet.At(Count.of(1))),
                left::get, left.isEmpty()).cutsInto(cuts, from, to);
        return cuts;
    }

    private static SortedSet<Long> walked(BitSet left, DateTranslation moved, long from, long to) {
        SortedSet<Long> cuts = new TreeSet<>();
        for (long edge : new long[] {moved.first(), moved.last() + 1}) {
            addIfBetween(cuts, edge, from, to);
        }
        long low = Math.max(FIRST_DAY, Math.min(LAST_DAY, from + moved.offsetDays()));
        long high = Math.max(FIRST_DAY, Math.min(LAST_DAY, to + moved.offsetDays()));
        for (long day = low + 1; day <= high; day++) {
            int now = LocalDate.ofEpochDay(day).getDayOfMonth();
            int before = LocalDate.ofEpochDay(day - 1).getDayOfMonth();
            if (left.get(now) != left.get(before)) {
                addIfBetween(cuts, day - moved.offsetDays(), from, to);
            }
        }
        return cuts;
    }

    private static void addIfBetween(SortedSet<Long> cuts, long day, long from, long to) {
        if (from < day && day <= to) {
            cuts.add(day);
        }
    }
}
