package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.List;
import java.util.Objects;
import java.util.function.Function;

/**
 * A comparison one side of which is a call of an operation carrying a fact, and the other a number
 * the same on every run.
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
 * @param against the number on the other side
 * @param written the relation the source wrote, read from the call's side: {@code call rel number}
 *                however the two were written round
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
            ValueStanding.ReadThrough<E> call =
                    under(callFirst ? comparison.left() : comparison.right(), at, sides);
            Core answered = Core.withoutStanding(call.value());
            AnOperationApplied applied = AnOperationApplied.of(answered);
            F fact = applied == null ? null : factOf.apply(applied.operation());
            if (fact == null) {
                continue;
            }
            ExactRatio against =
                    sides.constant(callFirst ? comparison.right() : comparison.left(), at);
            if (against == null) {
                return null;
            }
            Rel written = (callFirst ? comparison.claim() : comparison.claim().turned())
                    .statedRelation();
            return new ACallAgainstANumber<>(applied, answered, fact, call.at(), against, written);
        }
        return null;
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
