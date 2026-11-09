package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.observe.Figure;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which rows the search tries does not turn on how many values a parameter has that the question
 * does not read: nearest first is by how far the values taken are from the firsts added up, so a
 * row that needs another parameter at a later value is tried however long that parameter's list is.
 */
class AParameterTheQuestionDoesNotReadDoesNotDecideWhichRowsAreTriedTest {

    private static List<RowSearch.Built> values(String prefix, int count) {
        List<RowSearch.Built> out = new ArrayList<>();
        for (int i = 0; i < count; i++) {
            out.add(new RowSearch.Built(FixtureTemplate.string(prefix + i), null));
        }
        return out;
    }

    @Test
    void aLaterValueOfOneParameterIsTriedBesideAnyNumberOfValuesOfAnother() {
        for (int others : new int[] {1, 5, 300, 5000}) {
            List<List<RowSearch.Built>> each = List.of(values("a", others), values("b", 3));

            List<List<RowSearch.Built>> rows = RowSearch.rowsOf(each, new HashSet<>());

            assertTrue(rows.stream().anyMatch(row -> row.get(1).fixture()
                            .equals(FixtureTemplate.string("b2"))),
                    "the third value of the second is tried beside " + others + " values");
        }
    }

    @Test
    void theRowOfEveryParameterAtItsFirstIsTheFirstTried() {
        List<List<RowSearch.Built>> rows = RowSearch.rowsOf(
                List.of(values("a", 4), values("b", 4)), new HashSet<>());

        assertEquals(List.of(FixtureTemplate.string("a0"), FixtureTemplate.string("b0")),
                rows.getFirst().stream().map(RowSearch.Built::fixture).toList());
    }

    @Test
    void everyRowIsTriedOnceWhereTheyAreFewerThanTheSearchTries() {
        List<List<RowSearch.Built>> rows = RowSearch.rowsOf(
                List.of(values("a", 3), values("b", 2), values("c", 2)), new HashSet<>());

        Set<List<FixtureTemplate>> seen = new HashSet<>();
        rows.forEach(row -> seen.add(row.stream().map(RowSearch.Built::fixture).toList()));

        assertEquals(12, rows.size());
        assertEquals(12, seen.size());
    }

    @Test
    void theSearchStopsAtItsFigureAndSaysSo() {
        Set<Figure> stopped = new HashSet<>();

        List<List<RowSearch.Built>> rows = RowSearch.rowsOf(
                List.of(values("a", 300), values("b", 300)), stopped);

        assertEquals(RowSearch.MOST_VALUES, rows.size());
        assertEquals(1, stopped.size());
    }
}
