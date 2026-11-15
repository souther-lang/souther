package souther.compiler.query;

import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.RowOutcome;
import souther.compiler.partition.InputsRowsRanWith;

import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.IntStream;

/**
 * What the rows ran with, ordered so that the values of rows few others answered like come first.
 *
 * <p>A rewrite of a walk is told from the walk by a row where the two answer differently, and the
 * answers the body gave on the rows written are what is known of where that may be. Rows the body
 * answered alike on show the same thing, and a row it answered as few others did is where the rows
 * written show what an input can differ in. A list grown with a value such a row holds carries that
 * difference to a row the body answered otherwise, so those values are the first a search tries.
 *
 * <p>Taken in the order the rows were written instead, a module that happens to write the rows
 * that show a difference last has the search spend its runs on what the rows before them hold, and
 * what is decided turns on where a row is written.
 *
 * <p>An ordering and nothing else: every value is kept, so what a search may reach is the same and
 * only what it reaches first changes. Rows that share an answer with equally many are in the order
 * they were written, so where every row answered alike or every row answered differently, nothing
 * moves.
 */
final class ValuesOfRareAnswersFirst {

    private ValuesOfRareAnswersFirst() {}

    /** {@code ranWith} with the values of the rarest answers of {@code rows} first. */
    static InputsRowsRanWith of(InputsRowsRanWith ranWith, List<RowOutcome> rows) {
        return of(ranWith, rows, RowOutcome::answer, RowOutcome::inputs);
    }

    static <R> InputsRowsRanWith of(InputsRowsRanWith ranWith, List<R> rows,
                                    Function<R, Object> answer,
                                    Function<R, List<ObservedValue>> inputs) {
        Map<Object, Long> sharing = new HashMap<>();
        rows.forEach(row -> sharing.merge(answer.apply(row), 1L, Long::sum));
        List<Integer> rarestFirst = IntStream.range(0, rows.size()).boxed()
                .sorted(Comparator.comparingLong(at -> sharing.get(answer.apply(rows.get(at)))))
                .toList();
        Map<ObservedValue, Integer> firstHeldBy = new HashMap<>();
        for (int rank = 0; rank < rarestFirst.size(); rank++) {
            for (ObservedValue input : inputs.apply(rows.get(rarestFirst.get(rank)))) {
                holding(input, rank, firstHeldBy);
            }
        }
        return ranWith.orderedBy(value -> firstHeldBy.getOrDefault(value, Integer.MAX_VALUE));
    }

    /** {@code value} and every value inside it, held by {@code row} unless an earlier row held it. */
    private static void holding(ObservedValue value, int row, Map<ObservedValue, Integer> into) {
        into.putIfAbsent(value, row);
        switch (value) {
            case ObservedValue.Sequence sequence ->
                    sequence.elements().forEach(each -> holding(each, row, into));
            case ObservedValue.Constructed constructed ->
                    constructed.fields().values().forEach(each -> holding(each, row, into));
            case ObservedValue.Mapping mapping -> mapping.entries().forEach(each -> {
                holding(each.key(), row, into);
                holding(each.value(), row, into);
            });
            case ObservedValue.Bool _, ObservedValue.Integer _, ObservedValue.Decimal _,
                 ObservedValue.Text _, ObservedValue.Temporal _, ObservedValue.Unit _,
                 ObservedValue.Absent _, ObservedValue.Unknown _, ObservedValue.Truncated _ -> { }
        }
    }
}
