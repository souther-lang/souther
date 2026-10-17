package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;
import souther.compiler.types.Type;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Objects;
import java.util.Optional;
import java.util.function.Function;

/**
 * What holds of a number exactly where a comparison of something else holds: a comparison of the
 * number with written ones, joined by both and either, or settled before anything is asked.
 *
 * <p>The answer of a rule that reads a comparison of one thing as a comparison of another — a count
 * of units as the steps between two values, a remainder of a shifted value as the remainder of the
 * value, a rounded number as the number before rounding. What the rule says is a tree of comparisons
 * of the number it was turned into, and the reading that holds those comparisons is the reading of
 * any comparison, so the tree is the whole of what a rule hands over.
 *
 * <p><b>Settled by the range the number can be in, and not by a figure of this reader's.</b> A number
 * that can only be between two ends compares the same with every number outside them: past the end
 * it is above, every time. Said here from the ends the caller supplies — the carrier of the values
 * the steps count, the divisor a remainder lies below — so no reader carries a threshold of its own
 * for where a comparison stops being worth asking.
 *
 * <p><b>The numbers are exact, and written once.</b> A line a rule draws can be a half, or past what
 * a signed 64-bit number says, and is held as the number it is. It meets a type only where the
 * comparison is handed on, and there it is written as the source would write it beside a value of
 * the type ({@link #stated}), so no rule chooses a spelling and none is held to one.
 */
public sealed interface ConstantComparison {

    /** The number stands {@code rel} to {@code against}. */
    record Against(Rel rel, ExactRatio against) implements ConstantComparison {

        public Against {
            Objects.requireNonNull(rel, "the number stands some way");
            Objects.requireNonNull(against, "to some number");
        }
    }

    /** Whatever the number is, the comparison holds, or fails. */
    record Settled(boolean holds) implements ConstantComparison {}

    /** Both hold. */
    record Both(ConstantComparison first, ConstantComparison second)
            implements ConstantComparison {}

    /** One of the two holds. */
    record Either(ConstantComparison first, ConstantComparison second)
            implements ConstantComparison {}

    /**
     * The number standing {@code rel} to {@code against}, for a number that is between {@code least}
     * and {@code most}.
     *
     * <p>Settled where every number between the ends compares one way and no other.
     */
    static ConstantComparison of(Rel rel, BigInteger against, BigInteger least, BigInteger most) {
        boolean atLeast = rel.holds(least.compareTo(against));
        boolean atMost = rel.holds(most.compareTo(against));
        boolean inside = against.compareTo(least) >= 0 && against.compareTo(most) <= 0;
        boolean decided = switch (rel) {
            case GE, GT, LE, LT -> atLeast == atMost;
            case EQ -> !inside || least.equals(most);
            case NE -> !inside || least.equals(most);
        };
        return decided ? new Settled(atLeast) : new Against(rel, ExactRatio.of(against));
    }

    /**
     * {@code subject} standing {@code rel} to {@code against}, written as a comparison the source
     * could write of a value of the subject's type and a number — or null where no number written
     * beside one says {@code against}.
     *
     * <p>Beside an Int a whole number an Int says, beside a Decimal a decimal, and beside a Rational a
     * decimal read at its exact value, which is how an exact number meets any other (ADR-0116). So
     * what the reading of a comparison is handed is the comparison it already reads, and a half, or
     * a number past a signed 64-bit one, is a line on a Decimal or a Rational like any written there.
     */
    public static StatedComparison stated(Rel rel, Core subject, ExactRatio against) {
        Type type = subject.type();
        Core number;
        Core.BinaryReading reading = Core.BinaryReading.AS_THEY_STAND;
        if (type == Type.INT) {
            if (!against.isWhole()
                    || !(against.floor() instanceof ExactAnswer.Held<BigInteger>(var whole))
                    || whole.bitLength() > Long.SIZE - 1) {
                return null;
            }
            number = new Core.Int(whole.longValueExact(), Type.INT, subject.pos());
        } else if (type == Type.DECIMAL || type == Type.RATIONAL) {
            if (!(against.writtenDecimal()
                    instanceof ExactAnswer.Held<Optional<BigDecimal>>(var written))
                    || written.isEmpty()) {
                return null;
            }
            number = new Core.Decimal(written.get(), Type.DECIMAL, subject.pos());
            if (type == Type.RATIONAL) {
                reading = Core.BinaryReading.EXACT_NUMBERS;
            }
        } else {
            return null;
        }
        return new StatedComparison(ComparisonClaim.stating(rel), subject, number, reading);
    }

    /**
     * What holds exactly where a whole number stands {@code rel} to {@code n}, said through what
     * holds where it is at least a given one — or null where that is null for one of the two it is
     * asked at.
     *
     * <p>Above {@code n} is at least {@code n + 1}, below is not at least {@code n}, and equal is
     * both at least {@code n} and not at least {@code n + 1}. So a reader of a number that is a step
     * of something else says where the step is at least one number and nothing more.
     */
    static ConstantComparison ofAWholeNumber(Rel rel, BigInteger n,
                                             Function<BigInteger, ConstantComparison> atLeast) {
        BigInteger next = n.add(BigInteger.ONE);
        return switch (rel) {
            case GE -> atLeast.apply(n);
            case GT -> atLeast.apply(next);
            case LT -> denied(atLeast.apply(n));
            case LE -> denied(atLeast.apply(next));
            case EQ -> both(atLeast.apply(n), denied(atLeast.apply(next)));
            case NE -> either(denied(atLeast.apply(n)), atLeast.apply(next));
        };
    }

    /** What holds exactly where {@code comparison} does not; null where it is null. */
    static ConstantComparison denied(ConstantComparison comparison) {
        return switch (comparison) {
            case null -> null;
            case Against(Rel rel, ExactRatio against) -> new Against(rel.denied(), against);
            case Settled(boolean holds) -> new Settled(!holds);
            case Both(var first, var second) -> either(denied(first), denied(second));
            case Either(var first, var second) -> both(denied(first), denied(second));
        };
    }

    /** Both of these, settled where either settles it; null where either is null. */
    static ConstantComparison both(ConstantComparison first, ConstantComparison second) {
        if (first == null || second == null) {
            return null;
        }
        if (first instanceof Settled settled) {
            return settled.holds() ? second : settled;
        }
        if (second instanceof Settled settled) {
            return settled.holds() ? first : settled;
        }
        return new Both(first, second);
    }

    /** One of these, settled where either settles it; null where either is null. */
    static ConstantComparison either(ConstantComparison first, ConstantComparison second) {
        if (first == null || second == null) {
            return null;
        }
        if (first instanceof Settled settled) {
            return settled.holds() ? settled : second;
        }
        if (second instanceof Settled settled) {
            return settled.holds() ? settled : first;
        }
        return new Either(first, second);
    }
}
