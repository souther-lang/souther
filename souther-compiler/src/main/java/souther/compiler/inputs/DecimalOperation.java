package souther.compiler.inputs;

import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.types.BinOp;
import souther.exact.ExactDecimals;

import java.math.BigDecimal;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.TreeSet;

/**
 * A sum, a difference, a product or a negation of decimals a comparison works out, told so that a
 * row can be asked whether the program gets past it.
 *
 * <p>Whether a decimal operation has room for its digits and scale is not a region of the numbers
 * its operands come to: {@code 0} written at the scale of an {@code int}'s greatest value is the
 * number {@code 0}, and its product with {@code 4.0} has no room. So no region is stated here. A
 * row is asked by working the operation out on the row's own values by the rule the run time
 * works it out by ({@link ExactDecimals#timesWhereThereIsRoom}), and the row is computed where
 * every operation told is worked out. What is shown of a row is shown only by a row that was
 * built, and not of the rows the number stands for.
 *
 * <p>An operand is a decimal as the program wrote it ({@link Written}), the result of an operation
 * worked out before ({@link Worked}), or the number a row's values come to ({@link Formed}), which
 * is held at the fewest digits the number can be written with.
 *
 * @param op       the operator: add, subtract or multiply, or null for a negation
 * @param operands the one operand of a negation, or the two of the others in the order written
 * @param after    the operations, by where they are among those told, whose result this one is
 *                 worked out of, and theirs: each is worked out before it on every run
 */
public record DecimalOperation(BinOp op, List<Operand> operands, List<Integer> after) {

    public DecimalOperation {
        operands = List.copyOf(operands);
        after = List.copyOf(new TreeSet<>(after));
        if (operands.size() != (op == null ? 1 : 2)
                || (op != null && op != BinOp.ADD && op != BinOp.SUB && op != BinOp.MUL)) {
            throw new IllegalArgumentException("a decimal operation is a negation or the sum,"
                    + " difference or product of two decimals: " + op + " " + operands);
        }
    }

    /** What an operation is worked out of. */
    public sealed interface Operand {
    }

    /** A decimal written in the program, at the scale it is written. */
    public record Written(BigDecimal value) implements Operand {
        public Written {
            Objects.requireNonNull(value, "a decimal written in the program");
        }
    }

    /** What the operation told at {@code operation}, by where it is among those told, came to. */
    public record Worked(int operation) implements Operand {
    }

    /**
     * The number the terms of a row come to, each weighed, with {@code constant} added: a term
     * called by a key that the row does not name is a number the row does not have.
     */
    public record Formed(Map<Object, ExactRatio> coefs, ExactRatio constant) implements Operand {

        public Formed {
            if (coefs == null || constant == null
                    || coefs.keySet().stream().anyMatch(Objects::isNull)
                    || coefs.values().stream().anyMatch(Objects::isNull)) {
                throw new IllegalArgumentException("a number a row comes to weighs each of its"
                        + " terms by a number: " + coefs);
            }
            coefs = Map.copyOf(coefs);
        }

        /** The decimal this comes to at {@code values}, each term's value by its key; empty where
         *  a term has no value there or the number is none a decimal writes. */
        Optional<BigDecimal> at(Map<Object, ExactRatio> values) {
            ExactRatio sum = constant;
            for (Map.Entry<Object, ExactRatio> each : coefs.entrySet()) {
                ExactRatio value = values.get(each.getKey());
                if (value == null || sum == null) {
                    return Optional.empty();
                }
                sum = value.times(each.getValue()).flatMap(sum::plus).orNull();
            }
            if (sum == null) {
                return Optional.empty();
            }
            return switch (sum.writtenDecimal()) {
                case ExactAnswer.Held<Optional<BigDecimal>> written -> written.value();
                case ExactAnswer.Unheld<Optional<BigDecimal>> _ -> Optional.empty();
            };
        }
    }

    /**
     * Whether every operation of {@code all} is worked out on a row whose terms stand at
     * {@code values}, each by its key, in the order they are told — and so whether a run that
     * works them out gets past them. False where an operand is a number the row does not have.
     */
    public static boolean allCompleteAt(List<DecimalOperation> all, Map<Object, ExactRatio> values) {
        if (all.isEmpty()) {
            return true;
        }
        BigDecimal[] results = new BigDecimal[all.size()];
        for (int i = 0; i < all.size(); i++) {
            results[i] = all.get(i).workedOut(results, values);
            if (results[i] == null) {
                return false;
            }
        }
        return true;
    }

    /** The number this comes to, or null where the row has no operand for it or the run time has
     *  no room for the answer. */
    private BigDecimal workedOut(BigDecimal[] results, Map<Object, ExactRatio> values) {
        BigDecimal[] taken = new BigDecimal[operands.size()];
        for (int i = 0; i < taken.length; i++) {
            taken[i] = switch (operands.get(i)) {
                case Written written -> written.value();
                case Worked worked -> worked.operation() < results.length
                        ? results[worked.operation()] : null;
                case Formed formed -> formed.at(values).orElse(null);
            };
            if (taken[i] == null) {
                return null;
            }
        }
        return op == null ? taken[0].negate() : switch (op) {
            case ADD -> ExactDecimals.sumWhereThereIsRoom(taken[0], taken[1]);
            case SUB -> ExactDecimals.differenceWhereThereIsRoom(taken[0], taken[1]);
            default -> ExactDecimals.timesWhereThereIsRoom(taken[0], taken[1]);
        };
    }

    /** The same, with the operations it is worked out of moved {@code by} places later among
     *  those told. */
    public DecimalOperation shifted(int by) {
        return new DecimalOperation(op,
                operands.stream().map(each -> each instanceof Worked worked
                        ? (Operand) new Worked(worked.operation() + by) : each).toList(),
                after.stream().map(at -> at + by).toList());
    }
}
