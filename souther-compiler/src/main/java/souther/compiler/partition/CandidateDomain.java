package souther.compiler.partition;

import souther.compiler.numeric.AffinePreimage;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.UnheldNumber;

import java.math.BigDecimal;
import java.math.BigInteger;

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
 *   <li>{@link NotWorkedOut} — neither of the above: the exact arithmetic could not hold a number
 *       this needed to cut the coset to the run. Never a proof, and never {@link None}.
 * </ul>
 */
sealed interface CandidateDomain {

    /** No value of the position is both inside its run and on the coset. A proof. */
    record None() implements CandidateDomain {}

    /**
     * Neither a proof nor a set: a model's own decimals put a number this needed — an end of the
     * run, a multiplier, a step — far enough apart in scale from another that the exact arithmetic
     * could not hold it.
     *
     * <p>Told apart from {@link None} for the reason every such answer in this compiler is: a walk
     * that read this as empty would be a proof the rules do not license, over a position that may
     * hold values this simply could not name.
     */
    record NotWorkedOut(UnheldNumber why) implements CandidateDomain {

        public NotWorkedOut {
            if (why == null) {
                throw new IllegalArgumentException("not worked out, in one of the two ways it is not");
            }
        }
    }

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
            case AffinePreimage.None _ -> new None();
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
        ExactRatio from = on.from();
        ExactRatio by = on.by();
        Multiplied least = stepsTo(within.min(), from, by, true);
        if (least.unheld() != null) {
            return new NotWorkedOut(least.unheld());
        }
        Multiplied most = stepsTo(within.max(), from, by, false);
        if (most.unheld() != null) {
            return new NotWorkedOut(most.unheld());
        }
        if (least.at() != null && most.at() != null) {
            if (least.at().compareTo(most.at()) > 0) {
                return new None();
            }
            Multiplied first = at(from, by, least.at());
            if (first.unheld() != null) {
                return new NotWorkedOut(first.unheld());
            }
            if (least.at().compareTo(most.at()) == 0) {
                return new One(new Count(first.at().asWrittenDecimal()));
            }
            Multiplied last = at(from, by, most.at());
            return last.unheld() != null
                    ? new NotWorkedOut(last.unheld())
                    : new Walking(first.at().asWrittenDecimal(), by.asWrittenDecimal(),
                            last.at().asWrittenDecimal());
        }
        ExactRatio start = least.at() != null ? least.at() : most.at() != null ? most.at() : ExactRatio.ZERO;
        Multiplied startingAt = at(from, by, start);
        return startingAt.unheld() != null
                ? new NotWorkedOut(startingAt.unheld())
                : new Outward(startingAt.at().asWrittenDecimal(), by.asWrittenDecimal(), within);
    }

    /**
     * How many steps from {@code from} an end of the run lies, rounded inward, or which way the
     * exact arithmetic could not hold it, or {@link #noEnd} where the run has no end that way.
     *
     * <p>The division is asked for a whole number and never for a quotient, so a step that does not
     * divide the distance is no reason to lose the end. An end the rules exclude that falls exactly
     * on a step is one step further in.
     *
     * <p>Divided in ratios throughout, and never narrowed to a written decimal first: a distance the
     * exact arithmetic held is not thereby one a decimal of any particular scale holds, and dividing
     * two such decimals directly is the same scale-difference hazard this file exists to keep out of
     * a model's own sums. {@link ExactRatio#dividedBy} refuses only a divisor of nought, which
     * {@code by} is never; {@link ExactRatio#floor}/{@link ExactRatio#ceiling} are where the
     * quotient's own room to be held is actually asked.
     */
    private static Multiplied stepsTo(Endpoint end, ExactRatio from, ExactRatio by, boolean low) {
        if (end == null || !(end.at() instanceof Count count)) {
            return noEnd();
        }
        Multiplied away = switch (ExactRatio.of(count.at()).minus(from)) {
            case ExactAnswer.Unheld<ExactRatio> unheld -> new Multiplied(null, unheld.why());
            case ExactAnswer.Held<ExactRatio> apart -> new Multiplied(apart.value(), null);
        };
        if (away.unheld() != null) {
            return away;
        }
        ExactRatio quotient = away.at().dividedBy(by);
        ExactAnswer<BigInteger> rounded = low ? quotient.ceiling() : quotient.floor();
        if (!(rounded instanceof ExactAnswer.Held<BigInteger> heldSteps)) {
            return new Multiplied(null, ((ExactAnswer.Unheld<BigInteger>) rounded).why());
        }
        ExactRatio steps = ExactRatio.of(heldSteps.value());
        boolean onIt = by.times(steps).compareTo(away.at()) == 0;
        if (end.inclusive() || !onIt) {
            return new Multiplied(steps, null);
        }
        return switch (steps.plus(ExactRatio.of(low ? 1 : -1))) {
            case ExactAnswer.Unheld<ExactRatio> unheld -> new Multiplied(null, unheld.why());
            case ExactAnswer.Held<ExactRatio> held -> new Multiplied(held.value(), null);
        };
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
        ExactRatio from = on.from();
        ExactRatio by = on.by();
        Multiplied least = multiplier(within.min(), from, by);
        if (least.unheld() != null) {
            return new NotWorkedOut(least.unheld());
        }
        Multiplied most = multiplier(within.max(), from, by);
        if (most.unheld() != null) {
            return new NotWorkedOut(most.unheld());
        }
        boolean leastIsItsOwn = within.min() == null || within.min().inclusive();
        boolean mostIsItsOwn = within.max() == null || within.max().inclusive();
        if (least.at() == null && most.at() == null) {
            return somewhere(from, by, ExactRatio.ZERO);
        }
        if (least.at() == null) {
            Multiplied whole = wholeAt(most.at(), mostIsItsOwn, false);
            return whole.unheld() != null
                    ? new NotWorkedOut(whole.unheld()) : somewhere(from, by, whole.at());
        }
        if (most.at() == null) {
            Multiplied whole = wholeAt(least.at(), leastIsItsOwn, true);
            return whole.unheld() != null
                    ? new NotWorkedOut(whole.unheld()) : somewhere(from, by, whole.at());
        }
        int order = least.at().compareTo(most.at());
        if (order > 0 || (order == 0 && !(leastIsItsOwn && mostIsItsOwn))) {
            return new None();
        }
        if (order == 0) {
            // One point, and whether it is a member is decided rather than looked for.
            if (!least.at().fitsWrittenDecimal()) {
                return new None();
            }
            Multiplied one = at(from, by, least.at());
            return one.unheld() != null ? new NotWorkedOut(one.unheld())
                    : new One(new Count(one.at().asWrittenDecimal()));
        }
        Multiplied inside = between(least.at(), leastIsItsOwn, most.at());
        return inside.unheld() != null
                ? new NotWorkedOut(inside.unheld()) : somewhere(from, by, inside.at());
    }

    private static CandidateDomain somewhere(ExactRatio from, ExactRatio by, ExactRatio multiplier) {
        Multiplied member = at(from, by, multiplier);
        return member.unheld() != null ? new NotWorkedOut(member.unheld())
                : new Somewhere(new Count(member.at().asWrittenDecimal()));
    }

    /** A value the arithmetic held, or which way it could not hold one — never both, and neither
     *  where there was nothing to ask for in the first place ({@link #multiplier} on an end nothing
     *  bounds). An interface's members are public regardless, so this is one for the same reason
     *  every case of this sealed interface is — but it is not one of them, and no caller outside
     *  this file has a reason to name it. */
    record Multiplied(ExactRatio at, UnheldNumber unheld) {}

    private static Multiplied noEnd() {
        return new Multiplied(null, null);
    }

    /** Where an end of the run falls on the multiplier, or which way the exact arithmetic could not
     *  hold it, or {@link #noEnd} where the run has no end there or none this reads a number off. */
    private static Multiplied multiplier(Endpoint end, ExactRatio from, ExactRatio by) {
        if (end == null || !(end.at() instanceof Count count)) {
            return noEnd();
        }
        return switch (ExactRatio.of(count.at()).minus(from)) {
            case ExactAnswer.Unheld<ExactRatio> unheld -> new Multiplied(null, unheld.why());
            case ExactAnswer.Held<ExactRatio> apart -> new Multiplied(apart.value().dividedBy(by), null);
        };
    }

    /** The member at one multiplier, or which way the exact arithmetic could not hold it. Whole plus
     *  whole times a decimal is a decimal, so this is always a value a model writes once held. */
    private static Multiplied at(ExactRatio from, ExactRatio by, ExactRatio multiplier) {
        return switch (from.plus(by.times(multiplier))) {
            case ExactAnswer.Unheld<ExactRatio> unheld -> new Multiplied(null, unheld.why());
            case ExactAnswer.Held<ExactRatio> at -> new Multiplied(at.value(), null);
        };
    }

    /** The whole number at or past one end of the multiplier's run, or which way the exact
     *  arithmetic could not hold it. A decimal and needs no places written out. */
    private static Multiplied wholeAt(ExactRatio end, boolean itsOwn, boolean upward) {
        ExactAnswer<java.math.BigInteger> rounded = upward ? end.ceiling() : end.floor();
        if (!(rounded instanceof ExactAnswer.Held<java.math.BigInteger> held)) {
            return new Multiplied(null, ((ExactAnswer.Unheld<java.math.BigInteger>) rounded).why());
        }
        ExactRatio on = ExactRatio.of(held.value());
        if (itsOwn || on.compareTo(end) != 0) {
            return new Multiplied(on, null);
        }
        return switch (on.plus(ExactRatio.of(upward ? 1 : -1))) {
            case ExactAnswer.Unheld<ExactRatio> unheld -> new Multiplied(null, unheld.why());
            case ExactAnswer.Held<ExactRatio> moved -> new Multiplied(moved.value(), null);
        };
    }

    /**
     * A decimal strictly inside a run of multipliers wider than nothing, or which way the exact
     * arithmetic could not hold it.
     *
     * <p>At however many places it takes: past the point where a place is half the width, the value
     * rounded up to one lands under the far end whatever the near end excludes. Which is why there
     * is no allowance here to run out — the number of places is read off the ends rather than fixed,
     * and the two are exact ratios.
     */
    private static Multiplied between(ExactRatio least, boolean leastIsItsOwn, ExactRatio most) {
        if (most.minus(least) instanceof ExactAnswer.Unheld<ExactRatio> unheldApart) {
            return new Multiplied(null, unheldApart.why());
        }
        ExactRatio apart = most.minus(least).orNull();
        java.math.BigInteger places = java.math.BigInteger.ONE;
        ExactRatio half = apart.dividedBy(ExactRatio.of(2));
        while (ExactRatio.of(java.math.BigInteger.ONE, places).compareTo(half) > 0) {
            places = places.multiply(java.math.BigInteger.TEN);
        }
        ExactRatio step = ExactRatio.of(java.math.BigInteger.ONE, places);
        ExactAnswer<java.math.BigInteger> ceiling = least.times(ExactRatio.of(places)).ceiling();
        if (!(ceiling instanceof ExactAnswer.Held<java.math.BigInteger> held)) {
            return new Multiplied(null, ((ExactAnswer.Unheld<java.math.BigInteger>) ceiling).why());
        }
        ExactRatio on = ExactRatio.of(held.value()).times(step);
        if (leastIsItsOwn || on.compareTo(least) != 0) {
            return new Multiplied(on, null);
        }
        return switch (on.plus(step)) {
            case ExactAnswer.Unheld<ExactRatio> unheld -> new Multiplied(null, unheld.why());
            case ExactAnswer.Held<ExactRatio> moved -> new Multiplied(moved.value(), null);
        };
    }
}
