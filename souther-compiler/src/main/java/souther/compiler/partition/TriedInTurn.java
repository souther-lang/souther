package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.ExactRatio;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicReference;

/**
 * Every way of putting some of the input's numbers at the values tried for each, asked in turn
 * while a figure lasts, until one of them answers.
 *
 * <p>The walk two searches for a value of the input a run stops at share: one looking past what is
 * worked out before an operation ({@link StopAssessment}), and one looking past what a
 * construction asks ({@link ConstructionStopAssessment}). Which values each number is tried at, and
 * what is asked of one way of putting them, are each search's own. The ways are
 * {@link EveryWayOfChoosing}'s, each one asked a unit of {@link Tries}.
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
                       Tries left, Asking<R> ask) {
        List<List<ExactRatio>> values = new ArrayList<>(numbers.size());
        for (NumericTerm number : numbers) {
            values.add(tried.get(number));
        }
        AtomicReference<R> found = new AtomicReference<>();
        EveryWayOfChoosing.each(values, left, chosen -> {
            Map<NumericTerm, ExactRatio> at = new LinkedHashMap<>();
            for (int each = 0; each < numbers.size(); each++) {
                at.put(numbers.get(each), chosen.get(each));
            }
            found.set(ask.at(at));
            return found.get() == null;
        });
        return found.get();
    }
}
