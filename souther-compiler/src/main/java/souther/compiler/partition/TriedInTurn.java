package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.ExactRatio;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Every way of putting some of the input's numbers at the values tried for each, asked in turn
 * while a figure lasts, until one of them answers.
 *
 * <p>The walk two searches for a value of the input a run stops at share: one looking past what is
 * worked out before an operation ({@link StopAssessment}), and one looking past what a
 * construction asks ({@link ConstructionStopAssessment}). Which values each number is tried at, and
 * what is asked of one way of putting them, are each search's own. How the figure is spent, and
 * what it means for the walk to have run out of it, are said here and in
 * {@link StopAssessment.Tries}: a way asked for spends one unit, and where a unit is wanted and
 * there is none, or the last is spent with values still to try, the walk is cut short. A walk that
 * spent its last unit on its last way left nothing, and says nothing more.
 */
final class TriedInTurn {

    private TriedInTurn() {
    }

    /** What is asked of one way of putting the numbers. */
    @FunctionalInterface
    interface Asking<R> {
        R at(Map<NumericTerm, ExactRatio> values);
    }

    /** What {@code ask} first answers of a way of putting {@code numbers} at the values
     *  {@code tried} gives each, in the order of {@code numbers} and of the values, while
     *  {@code left} lasts — or null where none answers. */
    static <R> R first(List<NumericTerm> numbers, Map<NumericTerm, List<ExactRatio>> tried,
                       StopAssessment.Tries left, Asking<R> ask) {
        return each(numbers, 0, new LinkedHashMap<>(), tried, left, ask);
    }

    private static <R> R each(List<NumericTerm> numbers, int from,
                              Map<NumericTerm, ExactRatio> values,
                              Map<NumericTerm, List<ExactRatio>> tried, StopAssessment.Tries left,
                              Asking<R> ask) {
        if (from == numbers.size()) {
            return left.spend() ? ask.at(values) : null;
        }
        List<ExactRatio> tryAt = tried.get(numbers.get(from));
        for (int at = 0; at < tryAt.size(); at++) {
            values.put(numbers.get(from), tryAt.get(at));
            R found = each(numbers, from + 1, values, tried, left, ask);
            if (found != null) {
                return found;
            }
            if (left.spent()) {
                if (at < tryAt.size() - 1) {
                    left.leftSomethingUndone();
                }
                return null;
            }
        }
        values.remove(numbers.get(from));
        return null;
    }
}
