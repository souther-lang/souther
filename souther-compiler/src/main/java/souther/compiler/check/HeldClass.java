package souther.compiler.check;

import souther.compiler.numeric.Congruences;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Towards;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;

/**
 * The values of its order a position's own value is held to besides where it runs: the numbers the
 * rules leave between the ends of a range, which a range cannot say.
 *
 * <p>One type for every kind there is, with what is asked of one held beside it. Every reader asks
 * the same things of a class — whether a number is one of it, which of it a run holds, whether a run
 * holds any — and a reader handed one kind by its own name, or working one of those out for itself,
 * is a reader the next kind never reaches: a border that refused the fifteenth of a month to a value
 * held to the first of each and a search that offered it anyway would be two answers about one value.
 *
 * <p>Whether a run holds a member is answered exactly or not at all. A remainder's class is periodic
 * and a run is cut to it by arithmetic; the parts of a date come round with the calendar's cycle, and
 * a walk that went a cycle without meeting one has met every combination there is. So a class with
 * no member in a run is a proof that the run holds no value of it, and nothing here says so on the
 * strength of a walk that stopped short.
 */
public sealed interface HeldClass {

    /** The rules hold the value to no class. */
    record None() implements HeldClass {}

    /** The value leaves one remainder by each divisor, together {@code class_}. */
    record OfResidues(Congruences class_) implements HeldClass {}

    /** The value is a day whose date has the parts {@code parts} leaves. */
    record OfDays(DatePartsLeft parts) implements HeldClass {}

    /**
     * No value is of the class: remainders no number leaves together, parts no date has, or a class
     * with no member where the value runs.
     */
    record NoValue() implements HeldClass {}

    HeldClass NONE = new None();
    HeldClass NO_VALUE = new NoValue();

    /** Where a walk over a run of days with no end starts. */
    long A_CYCLE_STARTS = LocalDate.of(2000, 1, 1).toEpochDay();

    /**
     * The class a value of both is of: what is held to two is held to what they share, and a value
     * held to none is held to the other.
     */
    default HeldClass and(HeldClass other) {
        return switch (this) {
            case None _ -> other;
            case NoValue _ -> this;
            case OfResidues(Congruences one) -> switch (other) {
                case None _ -> this;
                case NoValue _ -> other;
                case OfResidues(Congruences two) -> one.meet(two) instanceof Congruences both
                        ? new OfResidues(both) : NO_VALUE;
                // A whole number and a day are values of two orders, which no value is both of.
                case OfDays _ -> NO_VALUE;
            };
            case OfDays(DatePartsLeft one) -> switch (other) {
                case None _ -> this;
                case NoValue _ -> other;
                case OfResidues _ -> NO_VALUE;
                case OfDays(DatePartsLeft two) -> {
                    DatePartsLeft both = one.and(two);
                    yield both.leaveADate() ? new OfDays(both) : NO_VALUE;
                }
            };
        };
    }

    /** Whether this class is of the numbers {@code on} counts, so that a number of that order is one
     *  it says anything of. A class of no kind says nothing of any. */
    default boolean countsOn(Carrier on) {
        return switch (this) {
            case OfResidues _ -> on instanceof Carrier.Whole;
            case OfDays _ -> on instanceof Carrier.Days;
            case None _, NoValue _ -> true;
        };
    }

    /** Whether {@code whole} is a value of this class. */
    default boolean holds(BigInteger whole) {
        return switch (this) {
            case None _ -> true;
            case NoValue _ -> false;
            case OfResidues(Congruences class_) ->
                    whole.mod(class_.modulus()).equals(class_.residue());
            case OfDays(DatePartsLeft parts) ->
                    whole.compareTo(BigInteger.valueOf(DatePartsLeft.FIRST_DAY)) >= 0
                            && whole.compareTo(BigInteger.valueOf(DatePartsLeft.LAST_DAY)) <= 0
                            && parts.holds(whole.longValueExact());
        };
    }

    /**
     * The members inside {@code run}, at most {@code most} of them, from the end nearest the line the
     * item is named for ({@link ClassMembers#within}).
     *
     * <p>Every member is inside the run and of the class. A run that holds none answers none and
     * says it left none, which is the proof {@link #within(NumericDomain.Bounds)} rests on.
     *
     * @param away which side of its line the run lies on, or null where no end is the near one
     */
    default ClassMembers within(NumericDomain.Bounds run, Towards away, int most) {
        return switch (this) {
            case None _ -> throw new IllegalStateException(
                    "a value held to no class has no members to walk: every value of the run is one");
            case NoValue _ -> ClassMembers.NONE;
            case OfResidues(Congruences class_) -> ClassMembers.within(class_, run, away, most);
            case OfDays(DatePartsLeft parts) -> daysWithin(parts, run, away, most);
        };
    }

    /**
     * The members inside {@code run} nearest {@code from}, at most {@code most} of them: by how far
     * they are from it, and above it before below it where two are as far.
     *
     * <p>The order a walk outward from a place takes, so a search that starts from a place and steps
     * past what it may not take reaches the same values whether the steps are of the order or of the
     * class.
     */
    default ClassMembers nearest(BigInteger from, NumericDomain.Bounds run, int most) {
        NumericDomain.Bounds above = run.meet(new NumericDomain.Bounds(
                Endpoint.inclusive(new Count(new BigDecimal(from))), null));
        NumericDomain.Bounds below = run.meet(new NumericDomain.Bounds(null,
                Endpoint.exclusive(new Count(new BigDecimal(from)))));
        ClassMembers up = above.holdsAValue() ? within(above, Towards.ABOVE, most)
                : ClassMembers.NONE;
        ClassMembers down = below.holdsAValue() ? within(below, Towards.BELOW, most)
                : ClassMembers.NONE;
        List<BigInteger> out = new ArrayList<>();
        int u = 0;
        int d = 0;
        while (out.size() < most && (u < up.values().size() || d < down.values().size())) {
            boolean takeUp = d >= down.values().size() || (u < up.values().size()
                    && up.values().get(u).subtract(from).abs()
                            .compareTo(down.values().get(d).subtract(from).abs()) <= 0);
            out.add(takeUp ? up.values().get(u++) : down.values().get(d++));
        }
        boolean left = u < up.values().size() || d < down.values().size()
                || up.stoppedShort() || down.stoppedShort();
        return new ClassMembers(out, left);
    }

    /**
     * This class with only what {@code range} leaves of it: the class itself where the range holds a
     * member, and {@link NoValue} where it holds none.
     *
     * <p>Said only where it is shown. A run holding no member is one walked to its end, or cut by the
     * arithmetic of a remainder, and either is a proof.
     */
    default HeldClass within(NumericDomain.Bounds range) {
        if (this instanceof None || this instanceof NoValue) {
            return this;
        }
        if (!range.holdsAValue()) {
            return NO_VALUE;
        }
        ClassMembers first = within(range, Towards.ABOVE, 1);
        return first.values().isEmpty() && !first.stoppedShort() ? NO_VALUE : this;
    }

    /**
     * {@code run} with each end it has moved inward to the nearest member of the class — crossed,
     * which is the run that holds nothing, where it holds none.
     *
     * <p>A search that names a place at either end names a member, where an end of the run itself is
     * one only by luck. An end with no member found inside it before a walk stopped stays where it
     * was, which is the run as wide as it was and so the sound answer with less.
     */
    default NumericDomain.Bounds hull(NumericDomain.Bounds run) {
        if (this instanceof None) {
            return run;
        }
        if (this instanceof NoValue || !run.holdsAValue()) {
            return crossed(run);
        }
        Endpoint low = run.min();
        Endpoint high = run.max();
        if (low != null) {
            ClassMembers first = within(run, Towards.ABOVE, 1);
            if (first.values().isEmpty()) {
                return first.stoppedShort() ? run : crossed(run);
            }
            low = Endpoint.inclusive(new Count(new BigDecimal(first.values().getFirst())));
        }
        if (high != null) {
            ClassMembers last = within(new NumericDomain.Bounds(null, run.max()).meet(
                    new NumericDomain.Bounds(low, null)), Towards.BELOW, 1);
            if (last.values().isEmpty()) {
                return last.stoppedShort() ? run : crossed(run);
            }
            high = Endpoint.inclusive(new Count(new BigDecimal(last.values().getFirst())));
        }
        return new NumericDomain.Bounds(low, high);
    }

    /** A run holding nothing, at the place {@code run} was asked about. */
    private static NumericDomain.Bounds crossed(NumericDomain.Bounds run) {
        Endpoint at = run.min() != null ? run.min() : run.max() != null ? run.max()
                : Endpoint.inclusive(Count.of(0));
        return new NumericDomain.Bounds(Endpoint.exclusive(at.at()), Endpoint.exclusive(at.at()));
    }

    /**
     * The days of {@code parts} inside {@code run}, walked from the near end. A run with no end at
     * all is walked from the start of a cycle, upward and then downward, as a run of whole numbers
     * with no end is walked outward from nought.
     */
    private static ClassMembers daysWithin(DatePartsLeft parts, NumericDomain.Bounds run,
                                           Towards away, int most) {
        BigInteger lowEnd = run.min() == null ? null : run.min().wholeAdmitted(true);
        BigInteger highEnd = run.max() == null ? null : run.max().wholeAdmitted(false);
        List<BigInteger> out = new ArrayList<>();
        if (lowEnd == null && highEnd == null) {
            DatePartsLeft.Walked up = parts.walk(BigInteger.valueOf(A_CYCLE_STARTS), null, true,
                    most - most / 2);
            DatePartsLeft.Walked down = parts.walk(BigInteger.valueOf(A_CYCLE_STARTS - 1), null,
                    false, most - up.days().size());
            up.days().forEach(day -> out.add(BigInteger.valueOf(day)));
            down.days().forEach(day -> out.add(BigInteger.valueOf(day)));
            return new ClassMembers(out, up.leftSome() || down.leftSome());
        }
        boolean fromBelow = lowEnd != null && (away != Towards.BELOW || highEnd == null);
        DatePartsLeft.Walked walked = fromBelow
                ? parts.walk(lowEnd, highEnd, true, most)
                : parts.walk(highEnd, lowEnd, false, most);
        walked.days().forEach(day -> out.add(BigInteger.valueOf(day)));
        return new ClassMembers(out, walked.leftSome());
    }
}
