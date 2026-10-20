package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.MeasurementStatus;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.InteractionEvidence;
import souther.compiler.query.Weakening;
import souther.compiler.report.AdequacyReport;

import java.util.Collections;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A total over the elements a comparison keeps is made of one decision per element, and a row makes
 * the combination of which elements it kept.
 *
 * <p>The comparison stands once, in the closure, and a run passes it once per element. A record of
 * which ways it came out holds the same two ways for a row that kept the first element and dropped
 * the second as for the row that did the opposite, so a measure that took no more than that would
 * count either row as having made both combinations.
 */
class RowsThatKeepDifferentElementsMakeDifferentCombinationsTest {

    private static final String MODEL = """
            module example.attendance

            data Row = { days: Int, pay: Int }

            behavior total : (first: Row, second: Row) -> Int

            let total (first, second) =
                List.sum(List.map(r -> r.pay, List.filter(r -> r.days >= 17, [ first, second ])))
            """;

    private static final String FIRST_ONLY = """
                | (Row { days = 20, pay = 100 }, Row { days = 5, pay = 200 }) -> 100
            """;

    private static final String SECOND_ONLY = """
                | (Row { days = 5, pay = 100 }, Row { days = 20, pay = 200 }) -> 200
            """;

    private static final String BOTH = """
                | (Row { days = 20, pay = 100 }, Row { days = 20, pay = 200 }) -> 300
            """;

    private static final String NEITHER = """
                | (Row { days = 5, pay = 100 }, Row { days = 5, pay = 200 }) -> 0
            """;

    @Test
    void theBodyHasACombinationForEveryChoiceOfWhichElementsAreKept() {
        assertEquals(4, evidenceOf(rows(FIRST_ONLY)).counted(), "two elements, kept or not");
    }

    @Test
    void aRowThatKeepsOneElementMakesOneCombination() {
        assertEquals(1, made(rows(FIRST_ONLY)));
    }

    @Test
    void theRowsThatKeepTheFirstAndThatKeepTheSecondMakeTwoDifferentOnes() {
        assertEquals(2, made(rows(FIRST_ONLY + SECOND_ONLY)),
                "a record of the ways the comparison came out cannot tell these two rows apart");
    }

    @Test
    void theSameRowTwiceMakesTheOneCombinationTwice() {
        assertEquals(1, made(rows(FIRST_ONLY + FIRST_ONLY)));
    }

    @Test
    void rowsThatKeepEveryChoiceOfElementsMakeEveryCombination() {
        InteractionEvidence evidence = evidenceOf(rows(FIRST_ONLY + SECOND_ONLY + BOTH + NEITHER));

        assertEquals(4, made(evidence));
        assertEquals(0, evidence.notMadeByRows().size());
    }

    /** The same total after a flatMap that writes each kept element out twice. */
    private static final String FLAT_MAPPED = """
            module example.attendance

            data Row = { days: Int, pay: Int }

            behavior total : (first: Row, second: Row) -> Int

            let total (first, second) =
                List.sum(List.map(r -> r.pay,
                    List.flatMap(r -> [ r, r ], List.filter(r -> r.days >= 17, [ first, second ]))))

            example total
            """;

    /**
     * Four occurrences of two applications are two decisions. The rows decide it, not the shape of
     * the meeting: one row makes one combination, and four rows make four, each counted by which
     * element it kept and not by how many times the kept element was written out.
     */
    @Test
    void aFlatMapAfterTheFilterDoesNotMultiplyTheDecisionsRowsMake() {
        String first = "    | (Row { days = 20, pay = 100 }, Row { days = 5, pay = 200 }) -> 200\n";
        String second = "    | (Row { days = 5, pay = 100 }, Row { days = 20, pay = 200 }) -> 400\n";
        String both = "    | (Row { days = 20, pay = 100 }, Row { days = 20, pay = 200 }) -> 600\n";
        String neither = "    | (Row { days = 5, pay = 100 }, Row { days = 5, pay = 200 }) -> 0\n";

        assertEquals(4, evidenceOf(FLAT_MAPPED + first).counted(), "two applications, kept or not");
        assertEquals(1, made(evidenceOf(FLAT_MAPPED + first)));
        assertEquals(2, made(evidenceOf(FLAT_MAPPED + first + second)));
        InteractionEvidence all = evidenceOf(FLAT_MAPPED + first + second + both + neither);
        assertEquals(4, made(all));
        assertEquals(0, all.notMadeByRows().size());
    }

    /**
     * More elements than a recording keeps visits of: the decisions are there, the sum is a
     * meeting, and it is not joined — because no claim can name the evaluations past the ones kept.
     * Nothing is claimed made, and nothing is reported as a combination no row makes.
     */
    @Test
    void aListOfMoreApplicationsThanAreRecordedIsAMeetingNotJoined() {
        String elements = String.join(", ", Collections.nCopies(40, "row"));
        AdequacyReport.BehaviorReport behavior = behaviorOf("""
                module example.attendance

                data Row = { days: Int, pay: Int }

                behavior total : (row: Row) -> Int

                let total (row) =
                    List.sum(List.map(r -> r.pay, List.filter(r -> r.days >= 17, [ %s ])))
                """.formatted(elements));

        assertEquals(1, behavior.evidence().interaction().asked().notJoined());
        assertEquals(0, behavior.evidence().interaction().counted());
        assertTrue(behavior.weakenedBy().causes().stream()
                        .anyMatch(Weakening.MeetingsNotJoined.class::isInstance),
                () -> "and the measure says it went without: " + behavior.weakenedBy());
    }

    /**
     * More elements than a group of combinations can be offered under: the meeting is there, and the
     * measure says it is not measured. Nothing is claimed made, and nothing is reported as a
     * combination no row makes.
     */
    @Test
    void aListTooLongToWalkIsAMeetingNotMeasuredAndNotOneThatIsAbsent() {
        InteractionEvidence evidence = evidenceOf("""
                module example.attendance

                data Row = { days: Int, pay: Int }

                behavior total : (row: Row) -> Int

                let total (row) =
                    List.sum(List.map(r -> r.pay, List.filter(r -> r.days >= 17,
                        [ row, row, row, row, row, row, row, row, row, row, row, row, row, row,
                          row, row, row, row ])))
                """);

        assertEquals(1, evidence.asked().read(), "the meeting is read");
        assertEquals(1, evidence.asked().notMeasured().size(), "and held back as not walked");
        assertEquals(0, evidence.counted(), "so no combination of it is claimed");
    }

    /**
     * An element kept by two comparisons is evaluated by the second only if the first kept it, so
     * the list does not say which evaluation is whose. The sum is a meeting this reading met and
     * could not join: no combination is reported made by evaluations that were never matched to an
     * element, and the behavior is not said to have had every combination of its decisions made.
     */
    @Test
    void elementsKeptByTwoComparisonsAreAMeetingNotJoinedAndTheMeasureSaysSo() {
        AdequacyReport.BehaviorReport behavior = behaviorOf("""
                module example.attendance

                data Row = { days: Int, pay: Int }

                behavior total : (first: Row, second: Row) -> Int

                let total (first, second) =
                    List.sum(List.map(r -> r.pay, List.filter(r -> r.pay > 0,
                        List.filter(r -> r.days >= 17, [ first, second ]))))

                example total
                    | (Row { days = 20, pay = 100 }, Row { days = 5, pay = 200 }) -> 100
                """);
        InteractionEvidence evidence = behavior.evidence().interaction();

        assertEquals(1, evidence.asked().read(), "the sum is a meeting");
        assertEquals(1, evidence.asked().notJoined(), "that was not joined");
        assertEquals(0, evidence.counted(), "so no combination of it is claimed");
        assertEquals(MeasurementStatus.PARTIAL, behavior.status(),
                () -> "and the behavior is short of a measurement: " + behavior.weakenedBy());
        assertTrue(behavior.weakenedBy().causes().stream()
                        .anyMatch(Weakening.MeetingsNotJoined.class::isInstance),
                () -> "which says it went without this: " + behavior.weakenedBy());
    }

    private static String rows(String rows) {
        return MODEL + "\nexample total\n" + rows;
    }

    private static int made(String model) {
        return made(evidenceOf(model));
    }

    private static int made(InteractionEvidence evidence) {
        return evidence.made().made().orElseThrow().met().size();
    }

    private static InteractionEvidence evidenceOf(String model) {
        return behaviorOf(model).evidence().interaction();
    }

    private static AdequacyReport.BehaviorReport behaviorOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).modules().getFirst().behaviors().getFirst();
    }
}
