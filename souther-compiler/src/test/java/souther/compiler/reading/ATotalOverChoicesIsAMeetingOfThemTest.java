package souther.compiler.reading;

import org.junit.jupiter.api.Test;

import souther.compiler.coverage.ControlPlace;
import souther.compiler.types.ConstructOccurrence;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static souther.compiler.reading.ReadInteractions.read;
import static souther.compiler.reading.ReadInteractions.shape;

/**
 * A total over the elements of a list written out consumes the choices each element makes into one
 * value, as {@code +} does between two of them. The list that holds them is no meeting: it is where
 * the values are kept, and the operation that adds them is where one is made of them.
 */
class ATotalOverChoicesIsAMeetingOfThemTest {

    private static final String PLUS = """
            module example.plus

            behavior total : (a: Bool, b: Bool) -> Int

            let total (a, b) = (if a then 100 else 0) + (if b then 200 else 0)
            """;

    private static final String SUM_OF_CHOICES = """
            module example.sumofchoices

            behavior total : (a: Bool, b: Bool) -> Int

            let total (a, b) = List.sum([ if a then 100 else 0, if b then 200 else 0 ])
            """;

    private static final String SUM_OF_ONE = """
            module example.sumofone

            behavior total : (a: Bool) -> Int

            let total (a) = List.sum([ if a then 100 else 0 ])
            """;

    private static final String LENGTH_OF_CHOICES = """
            module example.lengthofchoices

            behavior count : (a: Bool, b: Bool) -> Int

            let count (a, b) = List.length([ if a then 100 else 0, if b then 200 else 0 ])
            """;

    private static final String LIST_OF_CHOICES = """
            module example.listofchoices

            behavior pick : (a: Bool, b: Bool) -> List<Int>

            let pick (a, b) = [ if a then 100 else 0, if b then 200 else 0 ]
            """;

    private static final String FILTERED = """
            module example.filtered

            data Row = { days: Int, pay: Int }

            behavior total : (first: Row, second: Row) -> Int

            let total (first, second) =
                List.sum(List.map(r -> r.pay, List.filter(r -> r.days >= 17, [ first, second ])))
            """;

    /** The second filter is passed only by what the first kept, so which pass is whose is not
     *  something the list decides. */
    private static final String TWO_FILTERS = """
            module example.twofilters

            data Row = { days: Int, pay: Int }

            behavior total : (first: Row, second: Row) -> Int

            let total (first, second) =
                List.sum(List.map(r -> r.pay,
                    List.filter(r -> r.pay > 0, List.filter(r -> r.days >= 17, [ first, second ]))))
            """;

    /** More elements than the default budget of a group of combinations allows, and more than a
     *  run keeps visits of. */
    private static final String PAST_THE_PASSES_RECORDED = """
            module example.long

            data Row = { days: Int, pay: Int }

            behavior total : (row: Row) -> Int

            let total (row) =
                List.sum(List.map(r -> r.pay, List.filter(r -> r.days >= 17,
                    [ row, row, row, row, row, row, row, row, row, row, row, row, row, row, row,
                      row, row, row ])))
            """;

    /** A list the author does not write out. */
    private static final String A_LIST_INPUT = """
            module example.input

            data Row = { days: Int, pay: Int }

            behavior total : (rows: List<Row>) -> Int

            let total (rows) =
                List.sum(List.map(r -> r.pay, List.filter(r -> r.days >= 17, rows)))
            """;

    private static final String HELPER_TWICE = """
            module example.helper

            data Row = { days: Int, pay: Int }

            behavior total : (first: Row, second: Row) -> Int

            let kept (a: Row, b: Row): Int =
                List.sum(List.map(r -> r.pay, List.filter(r -> r.days >= 17, [ a, b ])))

            let total (first, second) = kept(first, second) + kept(second, first)
            """;

    /**
     * One helper called twice evaluates its comparison in two copies, each its own place in the
     * tree that runs and each counted on its own. A meeting of one copy is never held to a visit of
     * the other.
     */
    @Test
    void aHelperCalledTwiceIsTwoMeetingsEachHeldToItsOwnCopy() {
        List<Interaction> found = read(HELPER_TWICE, "total");

        assertEquals(List.of(List.of(2, 2), List.of(2, 2)), shape(found));
        List<Set<ConstructOccurrence>> copies = found.stream()
                .map(group -> group.factors().stream()
                        .flatMap(factor -> factor.outcomes().stream())
                        .flatMap(outcome -> outcome.claims().stream())
                        .map(claim -> ((ControlPlace.Outcome) claim.at()).occurrence())
                        .collect(Collectors.toSet()))
                .toList();
        assertEquals(1, copies.get(0).size(), "one copy of the comparison in a meeting");
        assertEquals(1, copies.get(1).size(), "and one in the other");
        assertNotEquals(copies.get(0), copies.get(1), "and not the same copy");
    }

    @Test
    void anElementKeptByTwoFiltersIsNotNamedByEitherPass() {
        assertEquals(List.of(), read(TWO_FILTERS, "total"),
                "which pass of the second comparison is whose depends on what the first kept");
    }

    /** The meeting is there however long the list is; that it is not measured is the budget's to
     *  say, as for any group too wide to walk. */
    @Test
    void aListLongerThanTheRunRecordsIsStillAMeeting() {
        List<List<Integer>> shape = shape(read(PAST_THE_PASSES_RECORDED, "total"));

        assertEquals(1, shape.size(), "one meeting: " + shape);
        assertEquals(18, shape.getFirst().size(), "of a decision per element: " + shape);
    }

    @Test
    void aListTheBodyDoesNotWriteOutIsNoMeeting() {
        assertEquals(List.of(), read(A_LIST_INPUT, "total"),
                "how many elements there are is not known, so no finite set of decisions is");
    }

    @Test
    void aTotalOverKeptElementsMeetsAsTheSameChoicesAddedDo() {
        List<Interaction> found = read(FILTERED, "total");
        assertEquals(List.of(List.of(2, 2)), shape(found), "one decision per element: " + found);
    }

    @Test
    void aSumOfChoicesMeetsAsTheSameChoicesAddedDo() {
        assertEquals(shape(read(PLUS, "total")), shape(read(SUM_OF_CHOICES, "total")),
                "the same value written with a total is the same two decisions meeting");
        assertEquals(List.of(List.of(2, 2)), shape(read(SUM_OF_CHOICES, "total")));
    }

    @Test
    void aTotalOverOneChoiceIsNoMeeting() {
        assertEquals(List.of(), read(SUM_OF_ONE, "total"),
                "one decision is consumed alone, so nothing is varied against it");
    }

    @Test
    void anOperationThatTakesNoValueOfTheElementsIsNoMeeting() {
        assertEquals(List.of(), read(LENGTH_OF_CHOICES, "count"),
                "how many elements there are is a function of neither decision");
    }

    @Test
    void aListOnlyBuiltOfChoicesIsNoMeeting() {
        assertEquals(List.of(), read(LIST_OF_CHOICES, "pick"),
                "a list is where two values arrive, not where one is made of them");
    }
}
