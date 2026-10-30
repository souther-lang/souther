package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.Objects;
import java.util.function.UnaryOperator;

/**
 * A comparison of a number rounded to a whole one, read as what it states of the number before it
 * was rounded.
 *
 * <p>The rounded number is a step of what was rounded, so it is no form of it and no reading of its
 * answer is arithmetic over it. What a comparison of it with a whole number states is exact all the
 * same: a line on the number before rounding, where the way of rounding puts it
 * ({@link WholeRounding}). {@code Rational.toInt(DOWN, x / 2) >= 100} is {@code x / 2 >= 100}, and
 * {@code Rational.toInt(HALF_UP, x / 2) >= 100} is {@code x / 2 >= 99.5}.
 *
 * <p><b>The way of rounding is a value.</b> The policy is read as any value is, through the names it
 * was given under, in the environment the comparison is read in, and the comparison is read only
 * where it is one case of the policy there. A policy chosen by the run is one case on each path the
 * walk reads to it; one that is no case where it is read has no one line, and is left unread rather
 * than taken as any of them.
 *
 * <p><b>The rounded number is an Int.</b> A rounding past the ends of one aborts, so a row that
 * reaches the comparison has a rounded number inside them, and a whole number past them is settled
 * by them.
 *
 * <p><b>Or a whole number of steps.</b> A rounding at a scale is a rounding to a whole number of
 * steps of ten to the minus that scale, and its comparison is read as that one's, of the number
 * taken in steps ({@link #atAScale}). {@code Decimal.round(2, HALF_UP, x) >= 30} is
 * {@code x >= 29.995}.
 */
public final class RoundedToAWholeNumber {

    private RoundedToAWholeNumber() {}

    /**
     * What a comparison of a rounded number states of the number before rounding.
     *
     * @param <E> the environment the number is read in
     * @param rounding the call that rounds it, as a value
     * @param rounded the number before rounding
     * @param at where the rounding was applied, which is where {@code rounded} is read
     * @param statement what holds of {@code rounded} exactly where the comparison holds, the
     *                  ends past which the rounding aborts included
     */
    public record Read<E>(Core rounding, Core rounded, E at, ConstantComparison statement) {

        public Read {
            Objects.requireNonNull(rounding, "a number is rounded by a call");
            Objects.requireNonNull(rounded, "a number is rounded");
            Objects.requireNonNull(at, "read somewhere");
            Objects.requireNonNull(statement, "and the comparison states something of it");
        }
    }

    /**
     * A call that rounds a number to a whole one, the policy written out as one of its cases.
     *
     * @param value the number before rounding
     * @param way what the policy does
     */
    public record Written(Core value, WholeRounding way) {

        public Written {
            Objects.requireNonNull(value, "a number is rounded");
            Objects.requireNonNull(way, "and a policy rounds it");
        }

        /**
         * The whole number this rounds {@code x} to, where the exact arithmetic holds the whole
         * numbers either side of it, and null otherwise.
         */
        public ExactRatio roundedFrom(ExactRatio x) {
            BigInteger whole = way.of(x);
            return whole == null ? null : ExactRatio.of(whole);
        }
    }

    /**
     * {@code call} as a rounding of a number to a whole one with a policy written out, or null where
     * it is no such call. A policy that is no written case is one the run chooses, and no way of
     * rounding is its.
     *
     * <p>The policy is the value {@code standing} says it stands at, as {@link #read} takes it: a
     * rounding in a helper's body is handed its policy by a name. What a run works out to get the
     * policy is not what it stands at, so a policy whose working out may end a run is no written
     * case.
     */
    public static Written written(Core call, UnaryOperator<Core> standing) {
        AnOperationApplied applied = AnOperationApplied.of(Core.withoutStanding(call));
        BoundOperationFact.RoundsToAStep rounds = applied == null ? null
                : DefaultBoundOperationFacts.get().roundsToAWholeNumber(applied.operation());
        Core value = rounds == null ? null : applied.argument(rounds.value());
        Core policy = rounds == null ? null : applied.argument(rounds.mode());
        WholeRounding way = policy == null || !WhatARunMayEndFor.endsNoneBeneath(policy) ? null
                : rounds.wayOf(standing.apply(policy));
        return value == null || way == null ? null : new Written(value, way);
    }

    /**
     * What {@code comparison}, read in {@code at}, states of the number one of its sides rounds — or
     * null where neither side is such a rounding, its policy is no one case where it is read, or the
     * other side is no whole number the same on every run.
     */
    public static <E> Read<E> read(StatedComparison comparison, E at,
                                   TheSignOfAnOrder.Sides<E> sides) {
        ACallAgainstANumber<E, BoundOperationFact.RoundsToAStep> rounding =
                ACallAgainstANumber.of(comparison, at, sides,
                        DefaultBoundOperationFacts.get()::roundsToAStep);
        if (rounding == null) {
            return null;
        }
        BoundOperationFact.RoundsToAStep rounds = rounding.fact();
        Core value = rounding.applied().argument(rounds.value());
        Core policy = rounding.applied().argument(rounds.mode());
        WholeRounding way = policy == null ? null
                : rounds.wayOf(sides.standing(policy, rounding.at()).value());
        if (value == null || way == null) {
            return null;
        }
        if (!rounds.toAWholeNumber()) {
            return atAScale(rounding, rounds, value, way, sides);
        }
        BigInteger whole = rounding.whole();
        if (whole == null) {
            return null;
        }
        // The ends of what the call answers, which a rounding past them aborts at.
        Carrier answered = Carrier.ofValue(rounding.answered().type(), sides.declarations());
        OrderedInterval ends = answered == null ? null : answered.extent();
        BigInteger least = ends == null ? null : WholeUnitsBetween.wholeNumberOf(ends.low());
        BigInteger most = ends == null ? null : WholeUnitsBetween.wholeNumberOf(ends.high());
        return least == null || most == null ? null : new Read<>(rounding.answered(), value,
                rounding.at(),
                statementOf(way, rounding.written(), whole, least, most));
    }

    /**
     * What a comparison of a number rounded at a scale states of the number before rounding — or
     * null where the scale is no whole number the same on every run.
     *
     * <p>Rounded at a scale {@code s}, a number is a whole number of steps of ten to the minus
     * {@code s}: the number times ten to the {@code s}, rounded to a whole number the same way. So
     * a comparison of it with {@code c} is one of that whole number with {@code c} times ten to the
     * {@code s}, read as a rounding to a whole number is; and where that is no whole number, a
     * whole number is at least it exactly where it is at least the whole number above it, and at
     * most it where it is at most the one below. What comes out is a statement of the number times
     * ten to the {@code s}, which is the same statement of the number with every line divided by
     * it. A decimal has no greatest or least, so no end settles any of it.
     */
    private static <E> Read<E> atAScale(
            ACallAgainstANumber<E, BoundOperationFact.RoundsToAStep> rounding,
            BoundOperationFact.RoundsToAStep rounds, Core value, WholeRounding way,
            TheSignOfAnOrder.Sides<E> sides) {
        Core scaleAt = rounding.applied().argument(rounds.scale());
        ExactRatio scale = scaleAt == null ? null : sides.constant(scaleAt, rounding.at());
        BigInteger places = scale == null || !scale.isWhole() ? null : scale.floor().orNull();
        ConstantComparison statement = places == null ? null
                : statementAtAScale(way, rounding.written(), rounding.against(), places);
        return statement == null ? null
                : new Read<>(rounding.answered(), value, rounding.at(), statement);
    }

    /**
     * What a number stands to exactly where its rounding by {@code way} at {@code places} stands
     * {@code rel} to {@code against} — or null where the run time rounds at no such scale, or the
     * exact arithmetic cannot hold a number of it.
     *
     * <p>The steps in one are ten to the scale, held as its exponents: a scale is written as a
     * number, and how far it is from nought is no measure of what this can afford to build.
     */
    static ConstantComparison statementAtAScale(WholeRounding way, Rel rel, ExactRatio against,
                                                BigInteger places) {
        if (!ARounding.answersAtAScale(places)) {
            return null;
        }
        ExactRatio steps = ExactRatio.tenTo(places.longValueExact());
        ExactRatio inSteps = against.times(steps).orNull();
        if (inSteps == null) {
            return null;
        }
        BigInteger onAStep = inSteps.isWhole() ? inSteps.floor().orNull() : null;
        if (inSteps.isWhole() && onAStep == null) {
            return null;
        }
        ConstantComparison onTheSteps = onAStep != null
                ? ConstantComparison.ofAWholeNumber(rel, onAStep, way::atLeast)
                : betweenTwoSteps(way, rel, inSteps);
        return onTheSteps == null ? null : dividedBy(onTheSteps, steps);
    }

    /**
     * What holds of a number exactly where its rounding by {@code way} stands {@code rel} to
     * {@code against}, which lies between two whole numbers: the rounding is at least it where it
     * is at least the whole number above, and at most it where it is at most the one below.
     */
    private static ConstantComparison betweenTwoSteps(WholeRounding way, Rel rel,
                                                      ExactRatio against) {
        BigInteger above = against.ceiling().orNull();
        BigInteger below = against.floor().orNull();
        if (above == null || below == null) {
            return null;
        }
        return switch (rel) {
            case GE, GT -> ConstantComparison.ofAWholeNumber(Rel.GE, above, way::atLeast);
            case LE, LT -> ConstantComparison.ofAWholeNumber(Rel.LE, below, way::atLeast);
            case EQ -> new ConstantComparison.Settled(false);
            case NE -> new ConstantComparison.Settled(true);
        };
    }

    /** {@code comparison} with every number it compares against divided by {@code by}, which is
     *  above nought; null where the exact arithmetic cannot hold one. */
    private static ConstantComparison dividedBy(ConstantComparison comparison, ExactRatio by) {
        return switch (comparison) {
            case ConstantComparison.Against(Rel rel, ExactRatio against) ->
                    against.dividedBy(by) instanceof ExactAnswer.Held<ExactRatio>(var line)
                            ? new ConstantComparison.Against(rel, line) : null;
            case ConstantComparison.Settled settled -> settled;
            case ConstantComparison.Both(var first, var second) ->
                    ConstantComparison.both(dividedBy(first, by), dividedBy(second, by));
            case ConstantComparison.Either(var first, var second) ->
                    ConstantComparison.either(dividedBy(first, by), dividedBy(second, by));
        };
    }

    /**
     * What the number before rounding stands to where its rounding by {@code way} stands
     * {@code rel} to {@code k}, for a rounded number from {@code least} to {@code most}.
     */
    static ConstantComparison statementOf(WholeRounding way, Rel rel, BigInteger k,
                                          BigInteger least, BigInteger most) {
        return ConstantComparison.ofAWholeNumber(rel, k, n -> atLeast(way, n, least, most));
    }

    /**
     * What holds of the number before rounding exactly where its rounding by {@code way} is at least
     * {@code k}, for a rounded number from {@code least} to {@code most}.
     */
    private static ConstantComparison atLeast(WholeRounding way, BigInteger k, BigInteger least,
                                              BigInteger most) {
        ConstantComparison rounded = ConstantComparison.of(Rel.GE, k, least, most);
        return rounded instanceof ConstantComparison.Against ? way.atLeast(k) : rounded;
    }
}
