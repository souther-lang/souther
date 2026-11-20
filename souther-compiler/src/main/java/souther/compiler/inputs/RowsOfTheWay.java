package souther.compiler.inputs;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

import java.util.List;

/**
 * Constraints over two numbers whose whole-number points are the rows of a way, every one of them
 * and no other.
 *
 * <p>What {@link TwoIntegerConstraints} answers is about points, and points are rows only here. A
 * reader that makes one of these says the constraints are the whole of what the declarations and
 * the way hold of the two numbers: the way states nothing else of them and declined nothing, each
 * number is the value at its place with every value its declarations hold taken, and no rule of
 * the declarations relates the two. Where it cannot say so it makes none, and a claim that some
 * value has a row beside it has nothing to rest on.
 *
 * <p>Not a proof of anything by being made: it is the reader's statement, kept as a type so that
 * a function asking which values have a row beside them takes this and cannot be handed
 * constraints that only bound the rows from outside.
 *
 * @param numbers     the two numbers, in the order the relation names them
 * @param constraints the constraints over them
 */
public record RowsOfTheWay(List<NumericTerm> numbers,
                           TwoIntegerConstraints<NumericTerm> constraints) {

    public RowsOfTheWay {
        numbers = List.copyOf(numbers);
        if (numbers.size() != 2) {
            throw new IllegalArgumentException("rows over two numbers: " + numbers);
        }
    }

    /**
     * The rows that the statements of the way {@code stated} leave the two {@code numbers}, each
     * held to the run {@code declared} says of it, or null where a statement is not about these
     * two alone or holds one apart from a value, or an end is not a number.
     *
     * <p>Says nothing of whether that is all the way and the declarations hold of them: the caller
     * who passes the statements has shown it, and that is what making one is.
     */
    public static RowsOfTheWay of(List<NumericTerm> numbers,
                                  List<TwoIntegerConstraints.Constraint<NumericTerm>> stated,
                                  List<NumericDomain.Bounds> declared) {
        TwoIntegerConstraints<NumericTerm> held =
                TwoIntegerConstraints.of(numbers.get(0), numbers.get(1), stated);
        for (int at = 0; at < 2 && held != null; at++) {
            held = heldTo(held, numbers.get(at), declared.get(at).min(), Rel.GE, Rel.GT);
            held = held == null ? null
                    : heldTo(held, numbers.get(at), declared.get(at).max(), Rel.LE, Rel.LT);
        }
        return held == null ? null : new RowsOfTheWay(numbers, held);
    }

    /** {@code number rel end}, {@code inclusive} or {@code exclusive} as the end is; none where
     *  there is no end, and null where it is no number. */
    private static TwoIntegerConstraints<NumericTerm> heldTo(
            TwoIntegerConstraints<NumericTerm> held, NumericTerm number, Endpoint end,
            Rel inclusive, Rel exclusive) {
        if (end == null) {
            return held;
        }
        if (!(end.at() instanceof Count count)) {
            return null;
        }
        return held.with(LinearForm.atomMinusConstant(number, count.exactly()),
                end.inclusive() ? inclusive : exclusive);
    }
}
