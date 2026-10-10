package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
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
    public record Read<E>(Core from, Core to, E at, Statement statement) {

        public Read {
            Objects.requireNonNull(from, "units are counted from something");
            Objects.requireNonNull(to, "and to something");
            Objects.requireNonNull(at, "read somewhere");
            Objects.requireNonNull(statement, "and the comparison states something of them");
        }
    }

    /** What holds of the number of steps, as relations of it to a whole number. */
    public sealed interface Statement {

        /** The steps stand {@code rel} to {@code against}. */
        record Steps(Rel rel, BigInteger against) implements Statement {

            public Steps {
                Objects.requireNonNull(rel, "the steps stand some way");
                Objects.requireNonNull(against, "to some number");
            }
        }

        /** Both of two statements hold. */
        record Both(Statement first, Statement second) implements Statement {}

        /** One of two statements holds. */
        record Either(Statement first, Statement second) implements Statement {}
    }

    /**
     * What {@code comparison}, read in {@code at}, states of the two values one of its sides is the
     * count of — or null where neither side is such a count, or the other side is no whole number
     * the same on every run.
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
            if (from == null || to == null || against == null || !against.isWhole()
                    || !(against.floor() instanceof ExactAnswer.Held<BigInteger>(var whole))) {
                return null;
            }
            // The relation the source wrote, read from the count's side: `count rel number`
            // however the two were written round.
            Rel written = (countFirst ? comparison.claim() : comparison.claim().turned())
                    .statedRelation();
            return new Read<>(from, to, count.at(),
                    statementOf(written, whole, counts.perUnit()));
        }
        return null;
    }

    /** What the steps stand to where the count stands {@code rel} to {@code n}. */
    static Statement statementOf(Rel rel, BigInteger n, long perUnit) {
        BigInteger unit = BigInteger.valueOf(perUnit);
        return switch (rel) {
            case GE -> atLeast(n, unit);
            case GT -> atLeast(n.add(BigInteger.ONE), unit);
            case LT -> below(n, unit);
            case LE -> below(n.add(BigInteger.ONE), unit);
            case EQ -> new Statement.Both(atLeast(n, unit), below(n.add(BigInteger.ONE), unit));
            case NE -> new Statement.Either(below(n, unit), atLeast(n.add(BigInteger.ONE), unit));
        };
    }

    private static Statement atLeast(BigInteger n, BigInteger unit) {
        return new Statement.Steps(Rel.GE, leastStepsReaching(n, unit));
    }

    private static Statement below(BigInteger n, BigInteger unit) {
        return new Statement.Steps(Rel.LT, leastStepsReaching(n, unit));
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
