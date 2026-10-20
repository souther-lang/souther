package souther.compiler.reading;

import org.junit.jupiter.api.Test;

import souther.compiler.coverage.ControlClaim;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.types.ConstructOccurrence;

import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static souther.compiler.reading.ReadInteractions.read;
import static souther.compiler.reading.ReadInteractions.readAll;
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

    /** A total over what each element is worth, with every element kept, whichever way it is
     *  written: the decisions are the same. */
    private static String totalOf(String body) {
        return """
                module example.worth

                data Row = { days: Int, pay: Int }

                behavior total : (first: Row, second: Row) -> Int

                let total (first, second) =
                    %s
                """.formatted(body);
    }

    private static final String AS_PLUS = "(if first.days >= 17 then first.pay else 0)"
            + " + (if second.days >= 17 then second.pay else 0)";

    private static final String AS_A_LIST = "List.sum([ if first.days >= 17 then first.pay else 0,"
            + " if second.days >= 17 then second.pay else 0 ])";

    private static final String AS_KEPT =
            "List.sum(List.map(r -> r.pay, List.filter(r -> r.days >= 17, [ first, second ])))";

    private static final String AS_WORTH =
            "List.sum(List.map(r -> if r.days >= 17 then r.pay else 0, [ first, second ]))";

    /**
     * What an element is worth and whether it is there are two ways an element decides a total, and
     * the total does not care which was written. Four ways of writing one sum of two choices are one
     * meeting of two decisions.
     */
    @Test
    void aSumOfTwoChoicesIsTheSameMeetingHoweverItsElementsAreDecided() {
        for (String body : List.of(AS_PLUS, AS_A_LIST, AS_KEPT, AS_WORTH)) {
            assertEquals(List.of(List.of(2, 2)), shape(read(totalOf(body), "total")), body);
        }
    }

    /** The decision of a value is the comparison evaluated on each application, as a keeping is. */
    @Test
    void aChoiceOfWhatEachElementIsWorthIsOneDecisionPerApplication() {
        List<Interaction> found = read(totalOf(AS_WORTH), "total");

        Set<Integer> visits = found.stream()
                .flatMap(group -> group.factors().stream())
                .flatMap(factor -> factor.outcomes().stream())
                .flatMap(outcome -> outcome.claims().stream())
                .map(claim -> ((ControlClaim.Visit.Nth) claim.visit()).index())
                .collect(Collectors.toSet());
        assertEquals(Set.of(0, 1), visits);
    }

    /**
     * A total of elements that are each worth what an empty total is worth is the same whichever are
     * kept, and the keeping decides nothing of it; a total of elements each worth one is a count of
     * what was kept, and does.
     */
    @Test
    void whatIsKeptIsADecisionOfTheTotalOnlyWhereTheTotalCanTellTheDifference() {
        String kept = "List.sum(List.map(r -> %s, List.filter(r -> r.days >= 17, [ first, second ])))";

        assertEquals(List.of(), read(totalOf(kept.formatted("0")), "total"));
        assertEquals(List.of(), readAll(totalOf(kept.formatted("0")), "total").notJoined());
        assertEquals(List.of(List.of(2, 2)), shape(read(totalOf(kept.formatted("1")), "total")));
    }

    /**
     * A choice of what an element is worth made after a filter is made of the elements it kept, so
     * which evaluation is whose depends on how the filter came out. The keeping alone is not the
     * meeting: leaving the choice out would be a reading that looks whole and is not.
     */
    @Test
    void aChoiceMadeAfterAFilterIsAMeetingNotJoinedAndNotLeftOut() {
        CoverageRead.Read read = readAll(totalOf("""
                List.sum(List.map(r -> if r.pay >= 100 then 2 else 1,
                    List.filter(r -> r.days >= 17, [ first, second ])))"""), "total");

        assertEquals(List.of(), read.interactions());
        assertEquals(List.of(WhyNotJoined.A_VALUE_CHOICE_NOT_NUMBERED), read.notJoined());
    }

    /** A fork beneath the names a value is written with is a decision all the same. */
    @Test
    void aChoiceBeneathANameTheValueIsWrittenWithIsNotReadAsNone() {
        CoverageRead.Read read = readAll(totalOf("""
                List.sum(List.map(r -> r + 1,
                    List.map(r -> if r.days >= 17 then r.pay else 0, [ first, second ])))"""),
                "total");

        assertEquals(List.of(), read.interactions());
        assertEquals(List.of(WhyNotJoined.A_VALUE_CHOICE_NOT_READ), read.notJoined());
    }

    private static final String NOTHING_KEPT = """
            module example.nothingkept

            data Row = { days: Int, pay: Int }

            behavior total : (first: Row, second: Row) -> Int

            let total (first, second) = List.sum(List.map(r -> r.pay, [ first, second ]))
            """;

    private static final String FLAT_MAPPED = """
            module example.flatmapped

            data Row = { days: Int, pay: Int }

            behavior total : (first: Row, second: Row) -> Int

            let total (first, second) =
                List.sum(List.map(r -> r.pay,
                    List.flatMap(r -> [ r, r ], List.filter(r -> r.days >= 17, [ first, second ]))))
            """;

    /**
     * A flatMap after the filter writes each kept element out twice, and the filter's closure was
     * applied to each of the two elements once. Four occurrences are two applications, so the sum
     * is made of two decisions and the comparison is evaluated twice.
     */
    @Test
    void elementsMadeSeveralOfByAFlatMapAreOneDecisionApiece() {
        List<Interaction> found = read(FLAT_MAPPED, "total");

        assertEquals(List.of(List.of(2, 2)), shape(found), "one decision per application");
        Set<Integer> visits = found.stream()
                .flatMap(group -> group.factors().stream())
                .flatMap(factor -> factor.outcomes().stream())
                .flatMap(outcome -> outcome.claims().stream())
                .map(claim -> ((ControlClaim.Visit.Nth) claim.visit()).index())
                .collect(Collectors.toSet());
        assertEquals(Set.of(0, 1), visits, "of the two evaluations a run makes");
    }

    @Test
    void anElementKeptByTwoFiltersIsAMeetingNotJoinedAndNotAbsent() {
        CoverageRead.Read read = readAll(TWO_FILTERS, "total");

        assertEquals(List.of(), read.interactions(),
                "which evaluation of the second comparison is whose depends on what the first kept");
        assertEquals(List.of(WhyNotJoined.KEPT_BY_SEVERAL), read.notJoined(),
                "and the sum is a meeting this reading met and did not join");
    }

    private static String keptBy(String condition, String total) {
        return """
                module example.kept

                data Row = { days: Int, pay: Int, active: Bool }

                behavior total : (first: Row, second: Row) -> Int

                let total (first, second) =
                    %s
                """.formatted(total.formatted(condition));
    }

    private static final String SUM_OF_KEPT =
            "List.sum(List.map(r -> r.pay, List.filter(r -> %s, [ first, second ])))";

    private static final String COUNT_OF_KEPT = "List.length(List.filter(r -> %s, [ first, second ]))";

    /**
     * That a decision exists is a fact about the container, and whether this reading can place it
     * is a fact about this reading. A truth read off a field, or a conjunction, keeps an element as
     * a comparison does; the sum is a meeting, one this does not join, and the measure says so.
     */
    @Test
    void aConditionThatIsNoSingleComparisonIsADecisionNotJoinedAndNotAbsent() {
        for (String condition : List.of("r.active", "r.days >= 17 && r.pay > 0")) {
            CoverageRead.Read read = readAll(keptBy(condition, SUM_OF_KEPT), "total");

            assertEquals(List.of(), read.interactions(), condition);
            assertEquals(List.of(WhyNotJoined.NOT_ONE_COMPARISON), read.notJoined(), condition);
        }
    }

    /** The number of the elements a comparison keeps is a function of what it kept, as their total
     *  is; the number of a list written out whole is not. */
    @Test
    void theCountOfWhatAComparisonKeepsIsAMeetingOfTheDecisionsThatKeepIt() {
        assertEquals(List.of(List.of(2, 2)),
                shape(read(keptBy("r.days >= 17", COUNT_OF_KEPT), "total")));
        assertEquals(List.of(), read(LENGTH_OF_CHOICES, "count"));
    }

    /**
     * An evaluation past those a recording keeps is a claim nothing observed could answer. The
     * decisions are there and the sum is a meeting; it is not joined, and says why.
     */
    @Test
    void aDecisionAboutAnEvaluationNoRecordingKeepsIsNotJoined() {
        String elements = String.join(", ", Collections.nCopies(40, "first"));
        CoverageRead.Read read = readAll("""
                module example.long

                data Row = { days: Int, pay: Int }

                behavior total : (first: Row) -> Int

                let total (first) =
                    List.sum(List.map(r -> r.pay, List.filter(r -> r.days >= 17, [ %s ])))
                """.formatted(elements), "total");

        assertEquals(List.of(), read.interactions());
        assertEquals(List.of(WhyNotJoined.MORE_VISITS_THAN_ARE_RECORDED), read.notJoined());
    }

    /** A comparison that is read, of a number no input position holds, is a decision a row cannot
     *  be steered by. It does not vanish from the sum for that. */
    @Test
    void aComparisonOfANumberNoInputHoldsIsADecisionNotJoinedAndNotAbsent() {
        CoverageRead.Read read = readAll(keptBy("r.days * 2 >= 34", SUM_OF_KEPT), "total");

        assertEquals(List.of(), read.interactions());
        assertEquals(List.of(WhyNotJoined.A_NUMBER_NO_INPUT_HOLDS), read.notJoined());
    }

    @Test
    void aSumWithNoDecisionInItIsNeitherAMeetingNorOneNotJoined() {
        CoverageRead.Read read = readAll(NOTHING_KEPT, "total");

        assertEquals(List.of(), read.interactions());
        assertEquals(List.of(), read.notJoined(), "a total of what nothing keeps decides nothing");
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
