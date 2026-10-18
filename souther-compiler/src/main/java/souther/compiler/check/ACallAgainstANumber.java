package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.function.Function;
import java.util.function.Predicate;

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
 * thought of, and the next one written would have found it under less. And the arithmetic it is
 * moved and scaled by is read by the reader's own arithmetic ({@link AffineForms#overTheCalls}), so
 * what a side comes to is said once, by the walk every reader of a number reads it with.
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
        Predicate<Core> isTheCall = e -> AnOperationApplied.of(e) instanceof AnOperationApplied
                applied && factOf.apply(applied.operation()) != null;
        for (boolean callFirst : List.of(true, false)) {
            Core asWritten = callFirst ? comparison.left() : comparison.right();
            // The call itself — an operation the arithmetic reads as a form of its arguments is
            // still the call here — or the arithmetic over it, as the reader reads arithmetic.
            ValueStanding.ReadThrough<E> stands = under(asWritten, at, sides);
            Weighed<E> side = isTheCall.test(Core.withoutStanding(stands.value()))
                    ? new Weighed<>(stands, ExactRatio.ONE, ExactRatio.ZERO)
                    : weighed(sides.overTheCalls(asWritten, at, isTheCall));
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
     * A side read as arithmetic over the calls, where it is one of them weighed by numbers the same
     * on every run — or null where it is no call, or more than one. So {@code compare(a, b) + 10 >=
     * 12} is the sign held at or above two.
     */
    private static <E> Weighed<E> weighed(LinearForm<AffineForms.ACall<E>> side) {
        if (side == null || side.coefs().size() != 1) {
            return null;
        }
        Map.Entry<AffineForms.ACall<E>, ExactRatio> only =
                side.coefs().entrySet().iterator().next();
        return new Weighed<>(new ValueStanding.ReadThrough<>(only.getKey().call(),
                only.getKey().at()), only.getValue(), side.constant());
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
