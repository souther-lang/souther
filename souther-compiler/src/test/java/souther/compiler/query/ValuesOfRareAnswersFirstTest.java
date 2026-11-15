package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.ObservedValue;
import souther.compiler.partition.InputsRowsRanWith;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the rows ran with has the values of rows few others answered like first, wherever the rows
 * were written, and no value is dropped.
 */
class ValuesOfRareAnswersFirstTest {

    /** A row, as far as what is ordered by it reads: what it was run with, and what came back. */
    private record Row(long input, long answered) {

        List<ObservedValue> inputs() {
            return List.of(new ObservedValue.Integer(input));
        }
    }

    private static InputsRowsRanWith ranWith(List<Row> written) {
        return InputsRowsRanWith.of(List.of(), List.of(written.stream()
                .map(each -> List.of(new InputsRowsRanWith.Taken(Type.INT, each.inputs().getFirst())))
                .toList()));
    }

    private static List<ObservedValue> ordered(List<Row> written) {
        return ValuesOfRareAnswersFirst.of(ranWith(written), written, Row::answered, Row::inputs)
                .of(Type.INT);
    }

    private static List<Long> values(List<ObservedValue> ordered) {
        return ordered.stream().map(each -> ((ObservedValue.Integer) each).value()).toList();
    }

    /** The row nobody else answered like holds the value that is first, wherever it was written. */
    @Test
    void theValueOfTheRowFewOthersAnsweredLikeIsFirstWhereverItIsWritten() {
        for (int rare = 0; rare < 4; rare++) {
            List<Row> written = new ArrayList<>(List.of(new Row(1, 0), new Row(2, 0), new Row(3, 0)));
            written.add(rare, new Row(9, 7));

            assertEquals(9L, values(ordered(written)).getFirst(), written::toString);
        }
    }

    @Test
    void everyValueIsKept() {
        List<Row> written = List.of(new Row(1, 0), new Row(2, 1), new Row(3, 0), new Row(4, 1),
                new Row(5, 2));

        List<Long> ordered = values(ordered(written));

        assertEquals(List.of(1L, 2L, 3L, 4L, 5L), ordered.stream().sorted().toList());
    }

    @Test
    void rowsThatShareTheirAnswerWithEquallyManyKeepTheOrderTheyWereWrittenIn() {
        assertEquals(List.of(1L, 2L, 3L), values(ordered(
                List.of(new Row(1, 0), new Row(2, 0), new Row(3, 0)))));
        assertEquals(List.of(1L, 2L, 3L), values(ordered(
                List.of(new Row(1, 7), new Row(2, 8), new Row(3, 9)))));
    }

    /** Of the answers, the rarer first. */
    @Test
    void ofTheAnswersTheRarerIsFirst() {
        List<Row> written = List.of(new Row(1, 0), new Row(2, 0), new Row(3, 0), new Row(4, 5),
                new Row(5, 5), new Row(6, 8));

        assertEquals(List.of(6L, 4L, 5L, 1L, 2L, 3L), values(ordered(written)));
    }

    /** A value a row does not hold is after every one a row does, in the order it was met. */
    @Test
    void valuesNoRowHoldsComeAfter() {
        List<Row> written = List.of(new Row(1, 0), new Row(2, 9));
        InputsRowsRanWith withAnother = InputsRowsRanWith.of(
                List.of(List.of(List.of(new InputsRowsRanWith.Taken(Type.INT,
                        new ObservedValue.Integer(7))))),
                List.of(written.stream().map(each -> List.of(new InputsRowsRanWith.Taken(Type.INT,
                        each.inputs().getFirst()))).toList()));

        List<Long> ordered = values(ValuesOfRareAnswersFirst
                .of(withAnother, written, Row::answered, Row::inputs).of(Type.INT));

        assertEquals(3, ordered.size());
        assertEquals(7L, ordered.getLast());
        assertTrue(ordered.containsAll(List.of(1L, 2L)));
    }
}
