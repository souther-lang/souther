package souther.compiler.partition;

import souther.compiler.check.DatePartsLeft;
import souther.compiler.semantics.TakenAs;

import java.time.LocalDate;
import java.time.Year;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.stream.IntStream;
import java.util.stream.LongStream;

/**
 * What parts of one date come to beside the date's own year, at the days of each year of the
 * calendar's cycle of four hundred years: each list of numbers some day gives, with the years of
 * the cycle a day giving it is in.
 *
 * <p>A part is a month or a day of the date moved by some days, or the year of the date so moved,
 * which is read as the years the move takes the date past its own: nought where it stays in its
 * year. The calendar comes round every four hundred years, so this is every list a date anywhere
 * gives, and where in the cycle it does.
 *
 * <p>The numbers a day gives are the calendar's at the days the moves reach, and those are fixed by
 * where the day is in its year and how long each year is from the date's to the farthest a move
 * reaches. So the years of the cycle with the same leap years about them give the same lists, and
 * one of them is read for all. A move of a whole number of cycles takes a date to the same month
 * and day four hundred years on, so a move is read as what it moves by less the nearest whole
 * cycles, and the years it moves past by those.
 *
 * <p>Only of the days every move is defined at, and every one in the middle of the calendar is: a
 * caller asking of the years at its ends, where a move runs out of dates, asks them itself.
 */
final class PartsOfADateOverACycle {

    static final int YEARS_OF_A_CYCLE = 400;

    /** The first year of the cycle the lists are read off, in the middle of the calendar. */
    private static final int FIRST_YEAR = 2000;

    /** The days of a year that is not a leap year, the fewest a year has. */
    private static final int DAYS_OF_A_SHORT_YEAR = 365;

    /** A part of the date moved by {@code offsetDays}. */
    record Moved(TakenAs.DatePart which, long offsetDays) {}

    /**
     * The numbers the parts come to at some day, in the order the parts were asked, and the years
     * of the cycle, by the year modulo four hundred, that a day giving them is in.
     */
    record Given(List<Integer> values, BitSet years) {

        Given {
            values = List.copyOf(values);
            years = (BitSet) years.clone();
        }

        /** The years, as a set the caller may change. */
        @Override
        public BitSet years() {
            return (BitSet) years.clone();
        }

        /** Whether a day giving these is in the year {@code ofTheCycle} of the cycle. */
        boolean in(int ofTheCycle) {
            return years.get(ofTheCycle);
        }
    }

    private PartsOfADateOverACycle() {
    }

    /** Every list {@code parts} come to at some day, in the order a day of the cycle first gives
     *  each. */
    static List<Given> of(List<Moved> parts) {
        return GIVEN.computeIfAbsent(List.copyOf(parts), PartsOfADateOverACycle::worked);
    }

    /** Answers by what was asked, which is all there is to them: the calendar and what the moves
     *  move by. A program asks the same few moves again and again. */
    private static final Map<List<Moved>, List<Given>> GIVEN = new ConcurrentHashMap<>();

    private static List<Given> worked(List<Moved> parts) {
        long half = DatePartsLeft.DAYS_OF_A_CYCLE / 2;
        long[] within = new long[parts.size()];
        int[] cycles = new int[parts.size()];
        long reach = 0;
        for (int i = 0; i < within.length; i++) {
            long offset = parts.get(i).offsetDays();
            long whole = Math.floorDiv(offset + half, DatePartsLeft.DAYS_OF_A_CYCLE);
            cycles[i] = Math.toIntExact(whole);
            within[i] = offset - whole * DatePartsLeft.DAYS_OF_A_CYCLE;
            reach = Math.max(reach, Math.abs(within[i]));
        }
        // A day of the year moved by the reach lands at most this many years either side of it.
        int around = (int) (reach / DAYS_OF_A_SHORT_YEAR) + 1;
        Map<List<Boolean>, BitSet> kinds = new LinkedHashMap<>();
        for (int year = FIRST_YEAR; year < FIRST_YEAR + YEARS_OF_A_CYCLE; year++) {
            List<Boolean> leap = IntStream.rangeClosed(year - around, year + around)
                    .mapToObj(Year::isLeap).toList();
            kinds.computeIfAbsent(leap, _ -> new BitSet(YEARS_OF_A_CYCLE))
                    .set(Math.floorMod(year, YEARS_OF_A_CYCLE));
        }
        Map<List<Integer>, BitSet> out = new LinkedHashMap<>();
        for (BitSet years : kinds.values()) {
            int year = FIRST_YEAR + years.nextSetBit(0);
            LongStream.rangeClosed(LocalDate.of(year, 1, 1).toEpochDay(),
                    LocalDate.of(year, 12, 31).toEpochDay()).forEach(day -> {
                        List<Integer> values = new ArrayList<>(within.length);
                        for (int i = 0; i < within.length; i++) {
                            LocalDate moved = LocalDate.ofEpochDay(day + within[i]);
                            TakenAs.DatePart which = parts.get(i).which();
                            values.add(which == TakenAs.DatePart.YEAR
                                    ? moved.getYear() - year + YEARS_OF_A_CYCLE * cycles[i]
                                    : which.of(moved));
                        }
                        out.computeIfAbsent(values, _ -> new BitSet(YEARS_OF_A_CYCLE))
                                .or(years);
                    });
        }
        List<Given> given = new ArrayList<>(out.size());
        out.forEach((values, years) -> given.add(new Given(values, years)));
        return List.copyOf(given);
    }
}
