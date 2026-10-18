package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;
import souther.compiler.types.BinOp;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.List;
import java.util.Objects;
import java.util.function.Function;

/**
 * A comparison one side of which is a call of an operation carrying a fact, alone or moved and
 * scaled by numbers the same on every run, and the other a number the same on every run.
 *
 * <p>Found here for every reader that turns such a comparison into one of what the call was given
 * ({@link TheSignOfAnOrder}, {@link WholeUnitsBetween}, {@link RoundedToAWholeNumber}): which side
 * is the call, and which way round the relation is read from it. A reader says only which fact it
 * reads and what the fact makes of the number.
 *
 * <p><b>The call is found under whatever it is written in.</b> A name is what it was given, and a
 * newtype's construction is the value it wraps, so {@code Yen(Rational.toInt(DOWN, total / 3))}
 * held against {@code Yen(100)} is the rounding held against a hundred, as it is for the arithmetic
 * ({@link AffineForms}). Each reader finding the call for itself found it under what that reader
 * thought of, and the next one written would have found it under less.
 *
 * @param <E> the environment the call is read in
 * @param <F> the fact the operation carries
 * @param applied the call, as the operation and its arguments
 * @param answered the call as a value, for what its answer is counted on
 * @param fact what the operation is declared to carry
 * @param at where the call was applied, which is where its arguments are read
 * @param against the number on the other side, with what the call was moved and scaled by taken
 *                over to it: twelve against {@code compare(a, b) + 10} is two against the call
 * @param written the relation the source wrote, read from the call's side: {@code call rel number}
 *                however the two were written round, and turned where the call was scaled below
 *                nought
 */
record ACallAgainstANumber<E, F>(AnOperationApplied applied, Core answered, F fact, E at,
                                 ExactRatio against, Rel written) {

    ACallAgainstANumber {
        Objects.requireNonNull(applied, "a call");
        Objects.requireNonNull(answered, "answering something");
        Objects.requireNonNull(fact, "of an operation carrying something");
        Objects.requireNonNull(at, "read somewhere");
        Objects.requireNonNull(against, "against a number");
        Objects.requireNonNull(written, "some way round");
    }

    /** The number on the other side as a whole number, or null where it is none. */
    BigInteger whole() {
        return against.isWhole() && against.floor() instanceof ExactAnswer.Held<BigInteger>(var n)
                ? n : null;
    }

    /**
     * The side of {@code comparison}, read in {@code at}, that is a call of an operation
     * {@code factOf} answers for, with the other side as a number — or null where neither side is
     * such a call or the other side is no number the same on every run.
     *
     * <p>A call on one side leaves nothing to try on the other: the call is no number the same on
     * every run, so the other side is never the call and this one the number.
     */
    static <E, F> ACallAgainstANumber<E, F> of(StatedComparison comparison, E at,
                                               TheSignOfAnOrder.Sides<E> sides,
                                               Function<ValueName, F> factOf) {
        for (boolean callFirst : List.of(true, false)) {
            Core asWritten = callFirst ? comparison.left() : comparison.right();
            // The call itself, or arithmetic over it on a side that is no number on every run: a
            // side that is one is walked into for nothing, and a chain of names under it folded
            // again at each link. Asked only of arithmetic, since what a side that is no
            // arithmetic comes to is no call weighed by anything, and working out whether it is a
            // number can cost as much as reading the comparison.
            ValueStanding.ReadThrough<E> stands = under(asWritten, at, sides);
            Weighed<E> side = called(stands, factOf);
            if (side == null && isArithmetic(stands)
                    && sides.constant(asWritten, at) == null) {
                side = weighed(asWritten, at, sides, factOf);
            }
            if (side == null) {
                continue;
            }
            ExactRatio other =
                    sides.constant(callFirst ? comparison.right() : comparison.left(), at);
            ExactRatio moved = other == null ? null : other.minus(side.offset()).orNull();
            ExactRatio against = moved == null ? null : moved.dividedBy(side.scale()).orNull();
            if (against == null) {
                return null;
            }
            Rel stated = (callFirst ? comparison.claim() : comparison.claim().turned())
                    .statedRelation();
            Rel written = side.scale().signum() > 0 ? stated : stated.turned();
            Core answered = Core.withoutStanding(side.call().value());
            AnOperationApplied applied = AnOperationApplied.of(answered);
            return new ACallAgainstANumber<>(applied, answered, factOf.apply(applied.operation()),
                    side.call().at(), against, written);
        }
        return null;
    }

    /**
     * A side that is the call weighed by numbers the same on every run: {@code scale · call +
     * offset}, with {@code scale} not nought.
     */
    private record Weighed<E>(ValueStanding.ReadThrough<E> call, ExactRatio scale,
                              ExactRatio offset) {}

    /**
     * {@code side} as a call of an operation {@code factOf} answers for, negated, added to, taken
     * from or multiplied by numbers the same on every run — or null where it is none. So {@code
     * compare(a, b) + 10 >= 12} is the sign held at or above two, as the arithmetic reads it
     * ({@link AffineForms}), and the comparison is of the call however the source moved its
     * number. A quotient is left out: what it comes to of a whole number is the arithmetic's to
     * say, and this does not say it a second time.
     */
    private static <E, F> Weighed<E> weighed(Core side, E at, TheSignOfAnOrder.Sides<E> sides,
                                             Function<ValueName, F> factOf) {
        ValueStanding.ReadThrough<E> stands = under(side, at, sides);
        Weighed<E> itself = called(stands, factOf);
        if (itself != null) {
            return itself;
        }
        return switch (Core.withoutStanding(stands.value())) {
            case Core.Neg n -> {
                Weighed<E> inner = weighed(n.operand(), stands.at(), sides, factOf);
                yield inner == null ? null : new Weighed<>(inner.call(), inner.scale().negated(),
                        inner.offset().negated());
            }
            case Core.Binary b when b.op() == BinOp.ADD || b.op() == BinOp.SUB -> {
                boolean taken = b.op() == BinOp.SUB;
                Beside<E> beside = beside(b, stands.at(), sides, factOf);
                if (beside == null) {
                    yield null;
                }
                Weighed<E> call = beside.call();
                ExactRatio offset = beside.callLeft()
                        ? (taken ? call.offset().minus(beside.number())
                                : call.offset().plus(beside.number())).orNull()
                        : (taken ? beside.number().minus(call.offset())
                                : beside.number().plus(call.offset())).orNull();
                yield offset == null ? null : new Weighed<>(call.call(),
                        taken && !beside.callLeft() ? call.scale().negated() : call.scale(),
                        offset);
            }
            case Core.Binary b when b.op() == BinOp.MUL -> {
                Beside<E> beside = beside(b, stands.at(), sides, factOf);
                if (beside == null || beside.number().isZero()) {
                    yield null;
                }
                ExactRatio scale = beside.call().scale().times(beside.number()).orNull();
                ExactRatio offset = beside.call().offset().times(beside.number()).orNull();
                yield scale == null || offset == null ? null
                        : new Weighed<>(beside.call().call(), scale, offset);
            }
            default -> null;
        };
    }

    /** Whether what {@code stands} for is arithmetic a call can be weighed in ({@link #weighed}). */
    private static <E> boolean isArithmetic(ValueStanding.ReadThrough<E> stands) {
        Core e = Core.withoutStanding(stands.value());
        return e instanceof Core.Neg || e instanceof Core.Binary b
                && (b.op() == BinOp.ADD || b.op() == BinOp.SUB || b.op() == BinOp.MUL);
    }

    /** {@code stands} as the call itself, weighed by nothing — or null where it is no call of an
     *  operation {@code factOf} answers for. */
    private static <E, F> Weighed<E> called(ValueStanding.ReadThrough<E> stands,
                                            Function<ValueName, F> factOf) {
        AnOperationApplied applied = AnOperationApplied.of(Core.withoutStanding(stands.value()));
        return applied != null && factOf.apply(applied.operation()) != null
                ? new Weighed<>(stands, ExactRatio.ONE, ExactRatio.ZERO) : null;
    }

    /** The call one operand of an operator is weighed by, beside the number the other is. */
    private record Beside<E>(Weighed<E> call, ExactRatio number, boolean callLeft) {}

    /**
     * The operand of {@code b} that weighs the call, beside the other as a number the same on every
     * run — or null where neither is. Only the operand beside a number is walked, so a value named
     * on both sides of an operator, and again under each of those, is not walked once for each way
     * down to it.
     */
    private static <E, F> Beside<E> beside(Core.Binary b, E at, TheSignOfAnOrder.Sides<E> sides,
                                           Function<ValueName, F> factOf) {
        ExactRatio right = sides.constant(b.right(), at);
        if (right != null) {
            Weighed<E> call = weighed(b.left(), at, sides, factOf);
            return call == null ? null : new Beside<>(call, right, true);
        }
        ExactRatio left = sides.constant(b.left(), at);
        Weighed<E> call = left == null ? null : weighed(b.right(), at, sides, factOf);
        return call == null ? null : new Beside<>(call, left, false);
    }

    /** What {@code side} is under the names it was given and the newtypes it was built as. */
    static <E> ValueStanding.ReadThrough<E> under(Core side, E at,
                                                         TheSignOfAnOrder.Sides<E> sides) {
        ValueStanding.ReadThrough<E> stands = sides.standing(side, at);
        while (Core.withoutStanding(stands.value()) instanceof Core.Construct built
                && sides.newtypes().of(built.typeName().key())) {
            stands = sides.standing(built.values().getFirst().value(), stands.at());
        }
        return stands;
    }
}
