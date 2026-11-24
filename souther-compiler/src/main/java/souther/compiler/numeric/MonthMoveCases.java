package souther.compiler.numeric;

import java.time.LocalDate;
import java.time.YearMonth;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.OptionalLong;
import java.util.Set;

/**
 * What a date moved by a count of months written out is, as cases over the numbers of the date it
 * is moved from.
 *
 * <p>A move by months is no move by any count of days ({@link CalendarMonths}), but where the month
 * of the date, the years round it that are leap years, and whether its day is past the end of the
 * month it lands in are known, it is: the first of the month lands on the first of the month it
 * lands in, however many days that is, and a day past the end of that month lands on its last. So
 * each case here is stated by what the date's month, its year's remainders and its day are, and
 * answers one number as a form of the date's own numbers.
 *
 * <p>The cases of one ask are exclusive and between them cover every date the move is defined at,
 * and the answer of each is what {@link CalendarMonths#movedBy} gives there. A year's leap status
 * is stated through the remainders the Gregorian rule is written in, so a case holds at every year
 * with those remainders and the calendar's four hundred years are all there is to tell apart.
 */
public final class MonthMoveCases {

    /** The most months a move is read in cases for: past it the leap years a move spans are more
     *  than a handful, and the cases more than a reading is made of. */
    public static final long MOST_MONTHS = 24;

    private static final int YEARS_THAT_REPEAT = 400;

    private MonthMoveCases() {
    }

    /** Which number of the date moved is asked. */
    public enum Asked {

        /** The day the date moved is on, counted as dates are counted. */
        DAY_NUMBER,

        /** The day of the month the date moved falls on. */
        DAY_OF_MONTH,

        /** The year the date moved falls in. */
        YEAR,

        /** The month the date moved falls in. */
        MONTH
    }

    /** A number of the date moved from. */
    public enum Of {

        /** The date as a day count. */
        DAY_NUMBER(0),

        /** The year it falls in. */
        YEAR(1),

        /** The month it falls in. */
        MONTH(2),

        /** The day of its month. */
        DAY_OF_MONTH(3),

        /** What its year leaves by four. */
        YEAR_BY_4(4),

        /** What its year leaves by one hundred. */
        YEAR_BY_100(5),

        /** What its year leaves by four hundred. */
        YEAR_BY_400(6);

        private final int id;

        Of(int id) {
            this.id = id;
        }

        /** The number that tells this one from the others in a derived origin; it does not move
         *  when the constants are reordered. */
        public int id() {
            return id;
        }
    }

    /** A number of the date standing in a relation to a number written out. */
    public record Stand(Of of, Rel rel, long value) {

        public Stand {
            Objects.requireNonNull(of, "a relation is of some number");
            Objects.requireNonNull(rel, "and stands some way");
        }

        /** Whether it holds where the number is {@code actual}. */
        public boolean holds(long actual) {
            return rel.holds(Long.compare(actual, value));
        }
    }

    /**
     * One case: where every relation in {@code given} holds, the number asked is
     * {@code constant} plus each number of the date weighed by what {@code weights} says.
     */
    public record Case(List<Stand> given, Map<Of, Long> weights, long constant) {

        public Case {
            given = List.copyOf(given);
            weights = Map.copyOf(weights);
        }
    }

    /** Whether a move by {@code months} is one read in cases: by no more than
     *  {@link #MOST_MONTHS} either way. */
    public static boolean reads(long months) {
        return months >= -MOST_MONTHS && months <= MOST_MONTHS;
    }

    /**
     * The months of a move of {@code first} and one of {@code then}, where the chain is read in
     * cases: none unless each move is one that is read, and the months they come to are too.
     *
     * <p>Each move and not only their sum, since a chain is a call in a call: one that moves by
     * more months than are read stands at a date no case says anything of, and a move back by as
     * many ends at the date the sum names without ever having been there. A chain that is none is
     * read as the calls it is written as.
     */
    public static OptionalLong chained(long first, long then) {
        if (!reads(first) || !reads(then) || !reads(first + then)) {
            return OptionalLong.empty();
        }
        return OptionalLong.of(first + then);
    }

    /**
     * The cases of what {@code asked} of a date moved by {@code months} is, or null where the move
     * is by more months than {@link #MOST_MONTHS}.
     *
     * @param firstOfItsMonth whether the date moved is the first of its month, so that its day is
     *                        no number to state and no case is one of a day past the end of the
     *                        month it lands in
     */
    public static List<Case> of(long months, Asked asked, boolean firstOfItsMonth) {
        if (!reads(months)) {
            return null;
        }
        List<Case> out = new ArrayList<>();
        if (asked == Asked.YEAR || asked == Asked.MONTH) {
            byTheMonths(months, asked, out);
            return out;
        }
        if (asked == Asked.DAY_OF_MONTH && firstOfItsMonth) {
            // The first of a month lands on the first of the month it lands in, whichever it is.
            out.add(new Case(List.of(new Stand(Of.MONTH, Rel.GE, 1),
                    new Stand(Of.MONTH, Rel.LE, CalendarMonths.A_YEAR)), Map.of(), 1));
            return out;
        }
        for (int month = 1; month <= CalendarMonths.A_YEAR; month++) {
            monthCases(months, month, asked, firstOfItsMonth, out);
        }
        return out;
    }

    /**
     * The year or the month moved into is the date's own year or month plus a number that is the
     * same for the months from one to another: the years the count of months from the first month
     * of the year reaches, or how far the month that count leaves by twelve is from the month.
     */
    private static void byTheMonths(long months, Asked asked, List<Case> out) {
        int from = 1;
        for (int month = 1; month <= CalendarMonths.A_YEAR; month++) {
            long plus = plusAtTheMonth(months, month, asked);
            boolean last = month == CalendarMonths.A_YEAR
                    || plus != plusAtTheMonth(months, month + 1, asked);
            if (last) {
                out.add(new Case(List.of(new Stand(Of.MONTH, Rel.GE, from),
                        new Stand(Of.MONTH, Rel.LE, month)),
                        Map.of(asked == Asked.YEAR ? Of.YEAR : Of.MONTH, 1L), plus));
                from = month + 1;
            }
        }
    }

    private static long plusAtTheMonth(long months, int month, Asked asked) {
        long counted = month - CalendarMonths.FIRST + months;
        return asked == Asked.YEAR ? Math.floorDiv(counted, CalendarMonths.A_YEAR)
                : Math.floorMod(counted, CalendarMonths.A_YEAR) + CalendarMonths.FIRST - month;
    }

    /**
     * What a date of {@code month} is moved to, in each way the years round it and its day can
     * stand that tells the answers apart.
     */
    private static void monthCases(long months, int month, Asked asked, boolean firstOfItsMonth,
                                   List<Case> out) {
        long years = Math.floorDiv(month - CalendarMonths.FIRST + months, CalendarMonths.A_YEAR);
        List<Integer> offsets = new ArrayList<>();
        for (long at = Math.min(0, years); at <= Math.max(0, years); at++) {
            offsets.add((int) at);
        }
        List<Set<Outcome>> outcomes = new ArrayList<>();
        for (int year = 0; year < YEARS_THAT_REPEAT; year++) {
            outcomes.add(outcomesAt(year, months, month, asked, firstOfItsMonth));
        }
        List<Integer> told = smallestThatTellsApart(offsets, outcomes);
        Map<List<LeapClass>, Set<Outcome>> byClasses = new LinkedHashMap<>();
        for (int year = 0; year < YEARS_THAT_REPEAT; year++) {
            List<LeapClass> classes = new ArrayList<>();
            for (int offset : told) {
                classes.add(LeapClass.of(year + offset));
            }
            byClasses.putIfAbsent(classes, outcomes.get(year));
        }
        for (Map.Entry<List<LeapClass>, Set<Outcome>> each : byClasses.entrySet()) {
            List<Stand> standing = new ArrayList<>();
            standing.add(new Stand(Of.MONTH, Rel.EQ, month));
            for (int at = 0; at < told.size(); at++) {
                each.getKey().get(at).standsFor(told.get(at), standing);
            }
            for (Outcome outcome : each.getValue()) {
                out.add(outcome.asACase(standing, asked, firstOfItsMonth));
            }
        }
    }

    /** What the date {@code month} of the year {@code year} is moved to, for each day it can be
     *  on, as what tells one answer from another. */
    private static Set<Outcome> outcomesAt(int year, long months, int month, Asked asked,
                                           boolean firstOfItsMonth) {
        LocalDate first = LocalDate.of(year, month, 1);
        LocalDate landed = CalendarMonths.movedBy(months, first);
        int length = landed.lengthOfMonth();
        boolean pastTheEnd = !firstOfItsMonth && YearMonth.of(year, month).lengthOfMonth() > length;
        long days = landed.toEpochDay() - first.toEpochDay();
        Set<Outcome> out = new LinkedHashSet<>();
        out.add(new Outcome(false, asked == Asked.DAY_NUMBER ? days : 0,
                pastTheEnd ? length : 0));
        if (pastTheEnd) {
            out.add(new Outcome(true, asked == Asked.DAY_NUMBER ? days : 0, length));
        }
        return out;
    }

    /**
     * The fewest of {@code offsets} whose years' leap classes say what a date is moved to: any two
     * years that agree on those classes have the same outcomes.
     */
    private static List<Integer> smallestThatTellsApart(List<Integer> offsets,
                                                        List<Set<Outcome>> outcomes) {
        for (int size = 0; size <= offsets.size(); size++) {
            for (int chosen = 0; chosen < 1 << offsets.size(); chosen++) {
                if (Integer.bitCount(chosen) != size) {
                    continue;
                }
                List<Integer> told = new ArrayList<>();
                for (int at = 0; at < offsets.size(); at++) {
                    if ((chosen >> at & 1) == 1) {
                        told.add(offsets.get(at));
                    }
                }
                if (tellsApart(told, outcomes)) {
                    return told;
                }
            }
        }
        throw new IllegalStateException("the years of a move tell its answers apart: " + offsets);
    }

    private static boolean tellsApart(List<Integer> told, List<Set<Outcome>> outcomes) {
        Map<List<LeapClass>, Set<Outcome>> seen = new LinkedHashMap<>();
        for (int year = 0; year < YEARS_THAT_REPEAT; year++) {
            List<LeapClass> classes = new ArrayList<>();
            for (int offset : told) {
                classes.add(LeapClass.of(year + offset));
            }
            Set<Outcome> before = seen.putIfAbsent(classes, outcomes.get(year));
            if (before != null && !before.equals(outcomes.get(year))) {
                return false;
            }
        }
        return true;
    }

    /**
     * What a date is moved to, as what tells it from the other places it can be moved.
     *
     * @param pastTheEnd whether its day is past the end of the month it lands in, and it lands on
     *                   the last day of it
     * @param days       how many days the first of the month moves, where the day count is asked
     * @param length     how long the month it lands in is, where that is told from its day
     */
    private record Outcome(boolean pastTheEnd, long days, int length) {

        Case asACase(List<Stand> standing, Asked asked, boolean firstOfItsMonth) {
            List<Stand> given = new ArrayList<>(standing);
            if (length > 0) {
                given.add(pastTheEnd ? new Stand(Of.DAY_OF_MONTH, Rel.GT, length)
                        : new Stand(Of.DAY_OF_MONTH, Rel.LE, length));
            }
            Map<Of, Long> weights = new LinkedHashMap<>();
            long constant;
            if (asked == Asked.DAY_NUMBER) {
                weights.put(Of.DAY_NUMBER, 1L);
                constant = days;
                if (pastTheEnd) {
                    weights.put(Of.DAY_OF_MONTH, -1L);
                    constant += length;
                }
            } else if (pastTheEnd) {
                constant = length;
            } else if (firstOfItsMonth) {
                constant = 1;
            } else {
                weights.put(Of.DAY_OF_MONTH, 1L);
                constant = 0;
            }
            return new Case(given, weights, constant);
        }
    }

    /** How a year stands to the Gregorian rule for a leap year, the four ways that tell the
     *  remainders it is stated through apart. */
    private enum LeapClass {

        /** A multiple of four that is no multiple of one hundred. */
        LEAP_BY_4,

        /** A multiple of four hundred. */
        LEAP_BY_400,

        /** No multiple of four. */
        COMMON_BY_4,

        /** A multiple of one hundred that is no multiple of four hundred. */
        COMMON_BY_100;

        static LeapClass of(int year) {
            if (Math.floorMod(year, 400) == 0) {
                return LEAP_BY_400;
            }
            if (Math.floorMod(year, 100) == 0) {
                return COMMON_BY_100;
            }
            return Math.floorMod(year, 4) == 0 ? LEAP_BY_4 : COMMON_BY_4;
        }

        /**
         * The relations on the year of the date that say the year {@code offset} years on from it
         * is of this class.
         */
        void standsFor(int offset, List<Stand> into) {
            long by4 = Math.floorMod(-offset, 4);
            long by100 = Math.floorMod(-offset, 100);
            long by400 = Math.floorMod(-offset, 400);
            switch (this) {
                case LEAP_BY_4 -> {
                    into.add(new Stand(Of.YEAR_BY_4, Rel.EQ, by4));
                    into.add(new Stand(Of.YEAR_BY_100, Rel.NE, by100));
                }
                case LEAP_BY_400 -> into.add(new Stand(Of.YEAR_BY_400, Rel.EQ, by400));
                case COMMON_BY_4 -> into.add(new Stand(Of.YEAR_BY_4, Rel.NE, by4));
                case COMMON_BY_100 -> {
                    into.add(new Stand(Of.YEAR_BY_4, Rel.EQ, by4));
                    into.add(new Stand(Of.YEAR_BY_100, Rel.EQ, by100));
                    into.add(new Stand(Of.YEAR_BY_400, Rel.NE, by400));
                }
            }
        }
    }
}
