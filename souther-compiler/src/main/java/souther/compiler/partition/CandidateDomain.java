package souther.compiler.partition;

import souther.compiler.numeric.AffinePreimage;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rational;

import java.math.BigDecimal;
import java.math.RoundingMode;

/**
 * The values one position of a form may stand at, and whether they can be walked to the end.
 *
 * <p>Two facts meet here and neither of them alone is the set. What the rules and the rest of the
 * form leave a position is a run between ends; what the coefficients of the rest can land on holds
 * the position to a coset ({@link AffinePreimage}). Used as a run alone, a position nothing bounds
 * was given whatever value sat inside it and a form whose level needed another said the search
 * stopped — the coset was known and was only ever asked to reject.
 *
 * <p><b>Five answers, and what tells them apart is what a search may conclude from running out.</b>
 * Nothing here decides anything about a row; what it decides is whether an empty-handed walk of it
 * was a walk of everything there was.
 *
 * <ul>
 *   <li>{@link None} — proved empty. A walk of it reaches the end at once.
 *   <li>{@link One} — one value, and proved to be the only one.
 *   <li>{@link Walking} — finitely many, in order, with a last. Only this and the two above can end.
 *   <li>{@link Outward} — a progression nothing bounds. It has a next value and no last.
 *   <li>{@link Somewhere} — a value out of a coset whose values fill. Between any two of them lies
 *       another, so there is no next value at all and the whole of what can be done with one is take
 *       the value it names.
 * </ul>
 */
sealed interface CandidateDomain {

    /** No value of the position is both inside its run and on the coset. A proof. */
    record None() implements CandidateDomain {}

    /** Exactly one value is, and nothing else has to be tried. */
    record One(Count at) implements CandidateDomain {}

    /**
     * The values from {@code first} to {@code last}, {@code by} apart.
     *
     * @param by always positive, so {@code first} is below {@code last} and the walk runs upward
     */
    record Walking(BigDecimal first, BigDecimal by, BigDecimal last) implements CandidateDomain {

        public Walking {
            if (by == null || by.signum() <= 0 || first == null || last == null
                    || first.compareTo(last) > 0) {
                throw new IllegalArgumentException(
                        "a run of candidates goes upward from its first to its last, a positive step"
                                + " at a time: " + first + " to " + last + " by " + by);
            }
        }
    }

    /**
     * A progression with a next value and no end, tried from {@code from} outward.
     *
     * <p>Outward and not upward. Which end is missing is not what decides where the answer lies, and
     * a walk that only went up would never reach a value below the one it started from.
     *
     * @param within the run itself, since a progression nothing bounds may still have one end
     */
    record Outward(BigDecimal from, BigDecimal by, NumericDomain.Bounds within)
            implements CandidateDomain {}

    /** One value of a coset whose values fill, which has no next value to step to. */
    record Somewhere(Count at) implements CandidateDomain {}

    /**
     * Where the position may stand: the coset, cut down to the run.
     *
     * <p>The position's own order is no argument here. Which kind of coset it is already says
     * whether its values step, since the coset is the image's answer about a position of that image
     * — asked of the carrier as well, the two could differ and there would be nothing to say which
     * of them the set was cut from.
     */
    static CandidateDomain of(AffinePreimage on, NumericDomain.Bounds within) {
        return switch (on) {
            case AffinePreimage.None ignored -> new None();
            case AffinePreimage.Stepping stepping -> stepping(stepping, within);
            case AffinePreimage.Filling filling -> filling(filling, within);
        };
    }

    /**
     * A progression cut to the run, which is a whole number of steps at each end.
     *
     * <p>Asked of the multiplier and not of the position: {@code from + by·k} is inside the run
     * exactly where {@code k} is inside the run moved by {@code from} and divided by {@code by}, and
     * the multiplier is a whole number where the position's value is one. Rounded inward at both
     * ends and the excluded end excluded, for the reason the walk's own rounding gives — a candidate
     * outside the run is one the rules refuse, and a search that offers it reads as every value
     * having been tried.
     */
    private static CandidateDomain stepping(AffinePreimage.Stepping on,
                                            NumericDomain.Bounds within) {
        BigDecimal from = on.from().asWrittenDecimal();
        BigDecimal by = on.by().asWrittenDecimal();
        if (from == null || by == null) {
            // A coset no decimal writes is one no value of a position takes, since a position holds
            // what a model can write down.
            return new None();
        }
        BigDecimal least = stepsTo(within.min(), from, by, true);
        BigDecimal most = stepsTo(within.max(), from, by, false);
        if (least != null && most != null) {
            if (least.compareTo(most) > 0) {
                return new None();
            }
            BigDecimal first = from.add(by.multiply(least));
            return least.compareTo(most) == 0
                    ? new One(new Count(first))
                    : new Walking(first, by, from.add(by.multiply(most)));
        }
        BigDecimal start = least != null ? least : most != null ? most : BigDecimal.ZERO;
        return new Outward(from.add(by.multiply(start)), by, within);
    }

    /**
     * How many steps from {@code from} an end of the run lies, rounded inward, or null where the run
     * has no end that way.
     *
     * <p>The division is asked for a whole number and never for a quotient, so a step that does not
     * divide the distance is no reason to lose the end. An end the rules exclude that falls exactly
     * on a step is one step further in.
     */
    private static BigDecimal stepsTo(Endpoint end, BigDecimal from, BigDecimal by, boolean low) {
        if (end == null || !(end.at() instanceof Count count)) {
            return null;
        }
        BigDecimal away = count.at().subtract(from);
        BigDecimal steps = away.divide(by, 0, low ? RoundingMode.CEILING : RoundingMode.FLOOR);
        boolean onIt = from.add(by.multiply(steps)).compareTo(count.at()) == 0;
        return end.inclusive() || !onIt ? steps : steps.add(BigDecimal.valueOf(low ? 1 : -1));
    }

    /**
     * A member of a coset whose values fill, inside the run.
     *
     * <p>Dense, so a run holding two of its members holds one between any two of them and there is
     * no walking it. What there is to do is name one, and naming one is arithmetic on the whole
     * numbers rather than a search: the members inside the run are exactly {@code from + by·d} for
     * the decimals {@code d} between the run's ends moved by {@code from} and divided by {@code by},
     * and a run wider than nothing holds one of those however narrow it is. Written the other way —
     * a member looked for at more and more decimal places until some allowance ran out — a run
     * narrower than the allowance reached came back with a value of the run that was no member of
     * the coset, which is the thing this whole type exists to stop.
     *
     * <p>An end this cannot read a number off is read as no end at all. Wider, and nothing here is a
     * proof except the two that come out of the ends having crossed or of one point that is no
     * member, both of which are decided on the numbers themselves.
     */
    private static CandidateDomain filling(AffinePreimage.Filling on, NumericDomain.Bounds within) {
        Rational from = on.from();
        Rational by = on.by();
        Rational least = multiplier(within.min(), from, by);
        Rational most = multiplier(within.max(), from, by);
        boolean leastIsItsOwn = within.min() == null || within.min().inclusive();
        boolean mostIsItsOwn = within.max() == null || within.max().inclusive();
        if (least == null && most == null) {
            return new Somewhere(at(from, by, Rational.ZERO));
        }
        if (least == null) {
            return new Somewhere(at(from, by, wholeAt(most, mostIsItsOwn, false)));
        }
        if (most == null) {
            return new Somewhere(at(from, by, wholeAt(least, leastIsItsOwn, true)));
        }
        int order = least.compareTo(most);
        if (order > 0 || (order == 0 && !(leastIsItsOwn && mostIsItsOwn))) {
            return new None();
        }
        if (order == 0) {
            // One point, and whether it is a member is decided rather than looked for.
            return least.asWrittenDecimal() == null ? new None() : new One(at(from, by, least));
        }
        return new Somewhere(at(from, by, between(least, leastIsItsOwn, most)));
    }

    /** Where an end of the run falls on the multiplier, or null where the run has no end there or
     *  none this reads a number off. */
    private static Rational multiplier(Endpoint end, Rational from, Rational by) {
        return end == null || !(end.at() instanceof Count count)
                ? null
                : Rational.of(count.at()).minus(from).dividedBy(by);
    }

    /** The member at one multiplier. Whole plus whole times a decimal is a decimal, so this is
     *  always a value a model writes. */
    private static Count at(Rational from, Rational by, Rational multiplier) {
        return new Count(from.plus(by.times(multiplier)).asWrittenDecimal());
    }

    /** The whole number at or past one end of the multiplier's run, which is a decimal and needs no
     *  places written out. */
    private static Rational wholeAt(Rational end, boolean itsOwn, boolean upward) {
        Rational on = Rational.of(upward ? end.ceiling() : end.floor());
        return itsOwn || on.compareTo(end) != 0
                ? on
                : on.plus(Rational.of(upward ? 1 : -1));
    }

    /**
     * A decimal strictly inside a run of multipliers wider than nothing.
     *
     * <p>At however many places it takes: past the point where a place is half the width, the value
     * rounded up to one lands under the far end whatever the near end excludes. Which is why there
     * is no allowance here to run out — the number of places is read off the ends rather than fixed,
     * and the two are exact ratios.
     */
    private static Rational between(Rational least, boolean leastIsItsOwn, Rational most) {
        java.math.BigInteger places = java.math.BigInteger.ONE;
        Rational half = most.minus(least).dividedBy(Rational.of(2));
        while (Rational.of(java.math.BigInteger.ONE, places).compareTo(half) > 0) {
            places = places.multiply(java.math.BigInteger.TEN);
        }
        Rational step = Rational.of(java.math.BigInteger.ONE, places);
        Rational on = Rational.of(least.times(Rational.of(places)).ceiling()).times(step);
        return leastIsItsOwn || on.compareTo(least) != 0 ? on : on.plus(step);
    }
}
