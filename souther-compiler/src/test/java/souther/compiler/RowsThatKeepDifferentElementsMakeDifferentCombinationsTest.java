package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.InteractionEvidence;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;

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
     * the list does not say which evaluation is whose. No meeting is read, and so no combination is
     * reported made by evaluations that were never matched to an element.
     */
    @Test
    void elementsKeptByTwoComparisonsAreNotJoinedToTheirEvaluations() {
        InteractionEvidence evidence = evidenceOf("""
                module example.attendance

                data Row = { days: Int, pay: Int }

                behavior total : (first: Row, second: Row) -> Int

                let total (first, second) =
                    List.sum(List.map(r -> r.pay, List.filter(r -> r.pay > 0,
                        List.filter(r -> r.days >= 17, [ first, second ]))))

                example total
                    | (Row { days = 20, pay = 100 }, Row { days = 5, pay = 200 }) -> 100
                """);

        assertEquals(0, evidence.asked().read(), "no meeting is read");
        assertEquals(0, evidence.counted());
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
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).modules().getFirst().behaviors().getFirst()
                .evidence().interaction();
    }
}
