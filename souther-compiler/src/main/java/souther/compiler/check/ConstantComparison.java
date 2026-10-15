package souther.compiler.check;

import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.Objects;

/**
 * What holds of a whole number exactly where a comparison of something else holds: a comparison of
 * the number with written ones, joined by both and either, or settled before anything is asked.
 *
 * <p>The answer of a rule that reads a comparison of one thing as a comparison of another — a count
 * of units as the steps between two values, a remainder of a shifted value as the remainder of the
 * value. What the rule says is a tree of comparisons of the number it was turned into, and the
 * reading that holds those comparisons is the reading of any comparison, so the tree is the whole of
 * what a rule hands over.
 *
 * <p><b>Settled by the range the number can be in, and not by a figure of this reader's.</b> A number
 * that can only be between two ends compares the same with every number outside them: past the end
 * it is above, every time. Said here from the ends the caller supplies — the carrier of the values
 * the steps count, the divisor a remainder lies below — so no reader carries a threshold of its own
 * for where a comparison stops being worth asking.
 */
public sealed interface ConstantComparison {

    /** The number stands {@code rel} to {@code against}. */
    record Against(Rel rel, BigInteger against) implements ConstantComparison {

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
     * <p>Settled where every number between the ends compares one way and no other. Null where the
     * comparison is a real one and {@code against} is more than a signed 64-bit number can say: what
     * hands it on writes a number into the tree it reads, and has no spelling for that one.
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
        if (decided) {
            return new Settled(atLeast);
        }
        return against.bitLength() > Long.SIZE - 1 ? null : new Against(rel, against);
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
