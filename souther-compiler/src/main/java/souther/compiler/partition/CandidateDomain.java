package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.AffinePreimage;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
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
    record Walking(BigDecimal first, BigDecimal by, BigDecimal last) implements CandidateDomain {}

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
     * @param carrier the position's own order, which is what says whether its values step
     */
    static CandidateDomain of(AffinePreimage on, NumericDomain.Bounds within, Carrier carrier) {
        return switch (on) {
            case AffinePreimage.None ignored -> new None();
            case AffinePreimage.Stepping stepping -> stepping(stepping, within);
            case AffinePreimage.Filling filling -> filling(filling, within, carrier);
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
     * <p>Dense, so a run holding two of its values holds one between any two of them and there is no
     * walking it. What there is to do is name one, and where the run has both ends the member has to
     * be named at enough decimal places to land between them — a coset of three holds
     * {@code 1, 1.3, 1.03}, and a run a tenth wide holds one of them however narrow it is.
     *
     * <p>Where the ends are so close that no member is written within
     * {@link #DIGITS_A_MEMBER_IS_NAMED_AT}, what comes back is a value of the run rather than
     * nothing: nothing is a proof here, and running out of digits is not one.
     */
    private static CandidateDomain filling(AffinePreimage.Filling on, NumericDomain.Bounds within,
                                           Carrier carrier) {
        BigDecimal from = on.from().asWrittenDecimal();
        BigDecimal by = on.by().asWrittenDecimal();
        if (from == null || by == null) {
            return new None();
        }
        if (within.min() == null && within.max() == null) {
            return new Somewhere(new Count(from));
        }
        Rational at = Rational.of(from);
        Rational step = Rational.of(by);
        for (int digits = 0; digits <= DIGITS_A_MEMBER_IS_NAMED_AT; digits++) {
            BigDecimal member = memberAt(within, at, step, digits);
            if (member != null && within.admits(new Count(member))) {
                // One end and the other at the same value is one member and not a run of them.
                return within.min() != null && within.max() != null
                        && within.min().at() instanceof Count low
                        && within.max().at() instanceof Count high
                        && low.at().compareTo(high.at()) == 0
                        ? new One(new Count(member))
                        : new Somewhere(new Count(member));
            }
        }
        Place inside = carrier.somethingInside(within.min(), within.max());
        return inside instanceof Count count ? new Somewhere(count) : new None();
    }

    /** How many decimal places a member of a dense coset is looked for at. */
    int DIGITS_A_MEMBER_IS_NAMED_AT = 24;

    /**
     * The member of {@code at + step·D} nearest the run's lower end with {@code digits} places in its
     * multiplier, or null where the run's ends are not numbers.
     */
    private static BigDecimal memberAt(NumericDomain.Bounds within, Rational at, Rational step,
                                       int digits) {
        Endpoint end = within.min() != null ? within.min() : within.max();
        if (!(end.at() instanceof Count count)) {
            return null;
        }
        Rational away = Rational.of(count.at()).minus(at).dividedBy(step);
        BigDecimal multiplier = away.asDecimal(
                within.min() != null ? RoundingMode.CEILING : RoundingMode.FLOOR, digits);
        return at.plus(step.times(Rational.of(multiplier))).asWrittenDecimal();
    }
}
