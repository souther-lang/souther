package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.check.DatePartsLeft;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.Congruences;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Towards;

import java.math.BigInteger;
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;

/**
 * The values of its order a position's own value is held to besides the run it is in: the numbers
 * the declarations leave between the ends of a range and that a range cannot say.
 *
 * <p>One type for every kind there is, because every reader of one asks the same two questions of
 * it — whether a number is one of them, and which of them a run holds — and a reader handed one kind
 * by its own name is a reader the next kind never reaches. A border that refused the fifteenth of a
 * month to a value held to the first and a search that offered it anyway would be two answers about
 * one value.
 */
sealed interface ClassHeldTo {

    /** The class the declarations {@code region} reads hold the value at {@code place} to, or null
     *  where they hold it to none. */
    static ClassHeldTo at(SearchRegion region, NumericTerm.ValueOf place) {
        Congruences residues = region.valueClassAt(place);
        if (residues != null) {
            return new OfWholeNumbers(residues);
        }
        DatePartsLeft parts = region.datePartsAt(place);
        return parts == null ? null : new OfDays(parts);
    }

    /** Whether this class is of the numbers {@code on} counts, so that a number of that order is
     *  one it says anything of. */
    boolean countsOn(Carrier on);

    /** Whether {@code whole} is a number of this class. */
    boolean holds(BigInteger whole);

    /**
     * The members of this class inside {@code run}, at most {@code most} of them, from the end of
     * the run nearest the line the item is named for ({@link ClassMembers#within}).
     *
     * @param away which side of its line the run lies on, or null where no end is the near one
     */
    ClassMembers within(NumericDomain.Bounds run, Towards away, int most);

    /** A class of whole numbers: those leaving one remainder by one divisor. */
    record OfWholeNumbers(Congruences residues) implements ClassHeldTo {

        @Override
        public boolean countsOn(Carrier on) {
            return on instanceof Carrier.Whole;
        }

        @Override
        public boolean holds(BigInteger whole) {
            return whole.mod(residues.modulus()).equals(residues.residue());
        }

        @Override
        public ClassMembers within(NumericDomain.Bounds run, Towards away, int most) {
            return ClassMembers.within(residues, run, away, most);
        }
    }

    /** The days whose dates have parts the declarations leave ({@link DatePartsLeft}). */
    record OfDays(DatePartsLeft parts) implements ClassHeldTo {

        /** Where a walk over a run with no end starts. */
        private static final long A_CYCLE_STARTS = LocalDate.of(2000, 1, 1).toEpochDay();

        @Override
        public boolean countsOn(Carrier on) {
            return on instanceof Carrier.Days;
        }

        @Override
        public boolean holds(BigInteger whole) {
            return whole.compareTo(BigInteger.valueOf(DatePartsLeft.FIRST_DAY)) >= 0
                    && whole.compareTo(BigInteger.valueOf(DatePartsLeft.LAST_DAY)) <= 0
                    && parts.holds(whole.longValueExact());
        }

        /**
         * The members inside {@code run}, walked from the near end. A run with no end at all is
         * walked from the start of a cycle, upward and then downward, as a run of whole numbers with
         * no end is walked outward from nought.
         */
        @Override
        public ClassMembers within(NumericDomain.Bounds run, Towards away, int most) {
            BigInteger lowEnd = run.min() == null ? null : ClassMembers.wholeEnd(run.min(), true);
            BigInteger highEnd = run.max() == null ? null : ClassMembers.wholeEnd(run.max(), false);
            long low = lowEnd == null ? DatePartsLeft.FIRST_DAY : clamp(lowEnd);
            long high = highEnd == null ? DatePartsLeft.LAST_DAY : clamp(highEnd);
            List<BigInteger> out = new ArrayList<>();
            if (lowEnd == null && highEnd == null) {
                DatePartsLeft.Walked up = parts.walk(A_CYCLE_STARTS, high, true, most - most / 2);
                DatePartsLeft.Walked down = parts.walk(A_CYCLE_STARTS - 1, low, false,
                        most - up.days().size());
                up.days().forEach(day -> out.add(BigInteger.valueOf(day)));
                down.days().forEach(day -> out.add(BigInteger.valueOf(day)));
                return new ClassMembers(out, up.leftSome() || down.leftSome());
            }
            boolean fromBelow = lowEnd != null && (away != Towards.BELOW || highEnd == null);
            DatePartsLeft.Walked walked = fromBelow ? parts.walk(low, high, true, most)
                    : parts.walk(high, low, false, most);
            walked.days().forEach(day -> out.add(BigInteger.valueOf(day)));
            return new ClassMembers(out, walked.leftSome());
        }

        private static long clamp(BigInteger day) {
            return day.max(BigInteger.valueOf(DatePartsLeft.FIRST_DAY))
                    .min(BigInteger.valueOf(DatePartsLeft.LAST_DAY)).longValueExact();
        }
    }
}
