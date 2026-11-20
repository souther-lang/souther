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
 * function asking which values have a row beside them takes this and cannot be handed constraints
 * that only bound the rows from outside.
 *
 * <p>Made only by {@link #of}, which asks for the facts the claim rests on as
 * {@link Premises}, one named fact for each, so that a reader making one has to state every one
 * and cannot leave one out. It cannot check them: what a reader shows of a way and its
 * declarations is the reader's to show, and these are the facts it is asked for.
 */
public final class RowsOfTheWay {

    /**
     * What a reader states of the way and the declarations, each a fact it has shown and the
     * constraints are the rows only if every one holds.
     *
     * @param eachNumberIsTheValueAtItsPlace   neither number is taken of something else, a part of
     *                                         a date or a count, which a rule between them may name
     *                                         in a way the constraints do not
     * @param everyValueOfItsDeclaredRunIsTaken each number takes every value its declarations hold,
     *                                         so that the run given is not wider than the values
     *                                         there are
     * @param noRuleOfTheDeclarationsRelatesThem no rule of the declarations relates the two
     *                                         numbers, none put aside as a reading of one line puts
     *                                         some: a rule left out is a point the constraints
     *                                         keep that is no row
     * @param theWayDeclinedNothing            every condition on the way to the comparison was
     *                                         read, so that no statement of it is missing here
     */
    public record Premises(boolean eachNumberIsTheValueAtItsPlace,
                           boolean everyValueOfItsDeclaredRunIsTaken,
                           boolean noRuleOfTheDeclarationsRelatesThem,
                           boolean theWayDeclinedNothing) {

        boolean allHold() {
            return eachNumberIsTheValueAtItsPlace && everyValueOfItsDeclaredRunIsTaken
                    && noRuleOfTheDeclarationsRelatesThem && theWayDeclinedNothing;
        }
    }

    private final List<NumericTerm> numbers;
    private final TwoIntegerConstraints<NumericTerm> constraints;

    private RowsOfTheWay(List<NumericTerm> numbers,
                         TwoIntegerConstraints<NumericTerm> constraints) {
        this.numbers = List.copyOf(numbers);
        this.constraints = constraints;
    }

    /** The two numbers, in the order the relation names them. */
    public List<NumericTerm> numbers() {
        return numbers;
    }

    /** The constraints over them. */
    public TwoIntegerConstraints<NumericTerm> constraints() {
        return constraints;
    }

    /**
     * The rows that the statements of the way {@code stated} leave the two {@code numbers}, each
     * held to the run {@code declared} says of it, or null where {@code premises} do not all hold,
     * a statement is not about these two alone or holds one apart from a value, or an end is not a
     * number.
     */
    public static RowsOfTheWay of(List<NumericTerm> numbers,
                                  List<TwoIntegerConstraints.Constraint<NumericTerm>> stated,
                                  List<NumericDomain.Bounds> declared, Premises premises) {
        if (numbers.size() != 2 || declared.size() != 2 || !premises.allHold()) {
            return null;
        }
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
