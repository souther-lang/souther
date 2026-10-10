package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.List;
import java.util.Objects;

/**
 * A comparison of a count of whole units between two values, read as what it states of the number
 * of steps between them.
 *
 * <p>Such a count drops what is left of a unit toward zero, so it is no form of the two values and
 * no reading of its answer is a sum of them. What a comparison of it states is a comparison of the
 * steps between the values, and that is exact: with {@code d} the steps from the first value to the
 * second and {@code u} the steps in a unit, the count is at least {@code n} exactly where
 * {@code d >= u * n} for a positive {@code n} and where {@code d >= u * n - (u - 1)} for any other,
 * since a negative difference of less than a unit is a count of nought and not of minus one.
 *
 * <p><b>The steps are the carrier's.</b> A fact of this kind is declared of an operation whose two
 * values are counted ({@link BoundOperationFact.CountsWholeUnitsBetween}), so what the steps between
 * two of them can be is read off the order the values are counted on: no further apart than its
 * first value and its last. A threshold past that is settled by it — every pair is on one side —
 * and one inside it that no signed 64-bit number can say is a comparison this does not read, and
 * says so by answering nothing.
 *
 * <p><b>One account for every reader of a condition.</b> Which side is the count, which way round
 * the relation is read from it, and which relations of the difference that comes to are answered
 * here, and a reader says only what is particular to its own environment
 * ({@link TheSignOfAnOrder.Sides}).
 */
public final class WholeUnitsBetween {

    private WholeUnitsBetween() {}

    /**
     * What a comparison of a count states of the steps from {@code from} to {@code to}.
     *
     * @param <E> the environment the two values are read in
     * @param from the value the units are counted from, read where the operation was applied
     * @param to the value they are counted to
     * @param at where the operation was applied, which is where the two are read
     * @param statement what holds of {@code to - from} exactly where the comparison holds
     */
    public record Read<E>(Core from, Core to, E at, ConstantComparison statement) {

        public Read {
            Objects.requireNonNull(from, "units are counted from something");
            Objects.requireNonNull(to, "and to something");
            Objects.requireNonNull(at, "read somewhere");
            Objects.requireNonNull(statement, "and the comparison states something of them");
        }
    }

    /**
     * What {@code comparison}, read in {@code at}, states of the two values one of its sides is the
     * count of — or null where neither side is such a count, the other side is no whole number the
     * same on every run, or what it states is no comparison this can write.
     */
    public static <E> Read<E> read(StatedComparison comparison, E at,
                                   TheSignOfAnOrder.Sides<E> sides) {
        for (boolean countFirst : List.of(true, false)) {
            AffineForms.ReadThrough<E> count =
                    sides.standing(countFirst ? comparison.left() : comparison.right(), at);
            AnOperationApplied applied = AnOperationApplied.of(Core.withoutStanding(count.value()));
            BoundOperationFact.CountsWholeUnitsBetween counts = applied == null ? null
                    : DefaultBoundOperationFacts.get().countsWholeUnitsBetween(applied.operation());
            if (counts == null) {
                continue;
            }
            Core from = applied.argument(counts.from());
            Core to = applied.argument(counts.to());
            ExactRatio against =
                    sides.constant(countFirst ? comparison.right() : comparison.left(), at);
            BigInteger widest = from == null ? null : widestDifference(from, sides);
            if (to == null || against == null || widest == null || !against.isWhole()
                    || !(against.floor() instanceof ExactAnswer.Held<BigInteger>(var whole))) {
                return null;
            }
            // The relation the source wrote, read from the count's side: `count rel number`
            // however the two were written round.
            Rel written = (countFirst ? comparison.claim() : comparison.claim().turned())
                    .statedRelation();
            ConstantComparison statement =
                    statementOf(written, whole, counts.perUnit(), widest);
            return statement == null ? null : new Read<>(from, to, count.at(), statement);
        }
        return null;
    }

    /**
     * How far apart two values of the order {@code value} is counted on can be: the steps from its
     * first value to its last. Null where the order has no first or no last, or ends that are no
     * whole number of steps.
     */
    private static <E> BigInteger widestDifference(Core value, TheSignOfAnOrder.Sides<E> sides) {
        Carrier carrier = Carrier.ofValue(value.type(), sides.declarations());
        if (carrier == null || !carrier.counts()) {
            return null;
        }
        OrderedInterval extent = carrier.extent();
        BigInteger first = wholeNumberOf(extent.low());
        BigInteger last = wholeNumberOf(extent.high());
        return first == null || last == null ? null : last.subtract(first).abs();
    }

    private static BigInteger wholeNumberOf(Endpoint end) {
        return end != null && end.at() instanceof Count count
                && count.exactly().floor() instanceof ExactAnswer.Held<BigInteger> whole
                ? whole.value() : null;
    }

    /**
     * What the steps stand to where the count stands {@code rel} to {@code n}, for two values no
     * further apart than {@code widest} steps — or null where that is a comparison with no spelling.
     */
    static ConstantComparison statementOf(Rel rel, BigInteger n, long perUnit,
                                          BigInteger widest) {
        BigInteger unit = BigInteger.valueOf(perUnit);
        BigInteger one = BigInteger.ONE;
        return switch (rel) {
            case GE -> atLeast(n, unit, widest);
            case GT -> atLeast(n.add(one), unit, widest);
            case LT -> below(n, unit, widest);
            case LE -> below(n.add(one), unit, widest);
            case EQ -> ConstantComparison.both(atLeast(n, unit, widest),
                    below(n.add(one), unit, widest));
            case NE -> ConstantComparison.either(below(n, unit, widest),
                    atLeast(n.add(one), unit, widest));
        };
    }

    private static ConstantComparison atLeast(BigInteger n, BigInteger unit, BigInteger widest) {
        return ConstantComparison.of(Rel.GE, leastStepsReaching(n, unit), widest.negate(), widest);
    }

    private static ConstantComparison below(BigInteger n, BigInteger unit, BigInteger widest) {
        return ConstantComparison.of(Rel.LT, leastStepsReaching(n, unit), widest.negate(), widest);
    }

    /**
     * The fewest steps whose count of units, truncated toward zero, is at least {@code n}.
     *
     * <p>A positive {@code n} is reached at {@code n} whole units. Any other is reached a unit less
     * one step early, because what is left over is dropped toward zero: a count of nought is
     * reached at minus fifty-nine steps over sixty-step units, and a count of minus one at minus
     * one hundred and nineteen.
     */
    static BigInteger leastStepsReaching(BigInteger n, BigInteger unit) {
        BigInteger whole = n.multiply(unit);
        return n.signum() > 0 ? whole : whole.subtract(unit.subtract(BigInteger.ONE));
    }
}
