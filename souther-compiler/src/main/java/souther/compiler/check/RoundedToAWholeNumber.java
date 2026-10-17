package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.numeric.Rel;
import souther.compiler.types.BinOp;
import souther.compiler.types.ConstructOccurrence;

import java.math.BigInteger;
import java.util.List;
import java.util.Objects;

/**
 * A comparison of a number rounded to a whole one, read as what it states of the number before it
 * was rounded.
 *
 * <p>The rounded number is a step of what was rounded, so it is no form of it and no reading of its
 * answer is arithmetic over it. What a comparison of it with a whole number states is exact all the
 * same: a line on the number before rounding, where the way of rounding puts it
 * ({@link WholeRounding}). {@code Rational.toInt(DOWN, x / 2) >= 100} is {@code x / 2 >= 100}, and
 * {@code Rational.toInt(HALF_UP, x / 2) >= 100} is {@code x / 2 >= 99.5}, which is said as twice
 * {@code x / 2} at least {@code 199} so the line is a whole number.
 *
 * <p><b>The way of rounding is a value.</b> The policy is read as any value is, through the names it
 * was given under, and the comparison is read only where it is one case of the policy on every run.
 * A policy the run decides has no one line, and is left unread rather than taken as any of them.
 *
 * <p><b>The rounded number is an Int.</b> A rounding past the ends of one aborts, so a row that
 * reaches the comparison has a rounded number inside them, and a whole number past them is settled
 * by them.
 */
public final class RoundedToAWholeNumber {

    private RoundedToAWholeNumber() {}

    /**
     * What a comparison of a rounded number states of the number before rounding.
     *
     * @param <E> the environment the number is read in
     * @param rounded the number before rounding — taken twice where the lines are at a half
     * @param at where the rounding was applied, which is where {@code rounded} is read
     * @param statement what holds of {@code rounded} exactly where the comparison holds
     */
    public record Read<E>(Core rounded, E at, ConstantComparison statement) {

        public Read {
            Objects.requireNonNull(rounded, "a number is rounded");
            Objects.requireNonNull(at, "read somewhere");
            Objects.requireNonNull(statement, "and the comparison states something of it");
        }
    }

    /**
     * What {@code comparison}, read in {@code at}, states of the number one of its sides rounds — or
     * null where neither side is such a rounding, its policy is not one case on every run, the
     * other side is no whole number the same on every run, or a line it comes to is more than a
     * signed 64-bit number can say.
     */
    public static <E> Read<E> read(StatedComparison comparison, E at,
                                   TheSignOfAnOrder.Sides<E> sides) {
        for (boolean roundedFirst : List.of(true, false)) {
            ValueStanding.ReadThrough<E> rounding =
                    sides.standing(roundedFirst ? comparison.left() : comparison.right(), at);
            Core call = Core.withoutStanding(rounding.value());
            AnOperationApplied applied = AnOperationApplied.of(call);
            BoundOperationFact.RoundsToAWholeNumber rounds = applied == null ? null
                    : DefaultBoundOperationFacts.get().roundsToAWholeNumber(applied.operation());
            if (rounds == null) {
                continue;
            }
            Core value = applied.argument(rounds.value());
            Core policy = applied.argument(rounds.mode());
            WholeRounding way = policy == null ? null
                    : rounds.wayOf(sides.standing(policy, rounding.at()).value());
            ExactRatio against =
                    sides.constant(roundedFirst ? comparison.right() : comparison.left(), at);
            Carrier carrier = Carrier.ofValue(call.type(), sides.declarations());
            OrderedInterval ends = carrier == null ? null : carrier.extent();
            BigInteger least = ends == null ? null : WholeUnitsBetween.wholeNumberOf(ends.low());
            BigInteger most = ends == null ? null : WholeUnitsBetween.wholeNumberOf(ends.high());
            if (value == null || way == null || against == null || least == null || most == null
                    || !against.isWhole()
                    || !(against.floor() instanceof ExactAnswer.Held<BigInteger>(var whole))) {
                return null;
            }
            // The relation the source wrote, read from the rounded side.
            Rel written = (roundedFirst ? comparison.claim() : comparison.claim().turned())
                    .statedRelation();
            ConstantComparison statement = statementOf(way, written, whole, least, most);
            return statement == null ? null
                    : new Read<>(taken(value, way), rounding.at(), statement);
        }
        return null;
    }

    /**
     * What the number before rounding — taken twice where {@code way}'s lines are at a half — stands
     * to where its rounding by {@code way} stands {@code rel} to {@code k}, for a rounded number from
     * {@code least} to {@code most}; null where a line is more than a signed 64-bit number can say.
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
        if (!(rounded instanceof ConstantComparison.Against)) {
            return rounded;
        }
        ConstantComparison.Against line = way.atLeast(k);
        return line.against().bitLength() > Long.SIZE - 1 ? null : line;
    }

    /** {@code value}, twice where {@code way}'s lines are at a half. */
    private static Core taken(Core value, WholeRounding way) {
        return way.linesAtAHalf()
                ? new Core.Binary(BinOp.ADD, value, value, Core.BinaryReading.AS_THEY_STAND,
                        ConstructOccurrence.unwritten(), value.type(), value.pos())
                : value;
    }
}
