package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value computed from several positions and cut at several places owes its ON and OFF points once
 * for each place, so rows at the points of one threshold of a table say nothing of the next.
 */
class EachThresholdOfADerivedValueOwesItsOwnOnAndOffPointsTest {

    private static final String MISSING_ON = "no row is at the ON point";
    private static final String MISSING_OFF = "no row is at the OFF point";

    private static String table(int top) {
        return """
                module demo

                data N = { v: Int }
                    invariant v >= 0
                data Row = { grade: Int, lowerBound: Int }
                let table: List<Row> = [ Row { grade = 1, lowerBound = 0 },
                                         Row { grade = 2, lowerBound = 100 },
                                         Row { grade = 3, lowerBound = %d } ]
                let gradeOf (m: Int): Int =
                    List.fold((acc, r) -> if r.lowerBound <= m then r.grade else acc, 0, table)

                behavior f : (a: N, b: N) -> Int

                let f (a, b) =
                    gradeOf(a.v + b.v)

                """.formatted(top);
    }

    private static final String AT_100 = """
            example f
                | (N { v = 100 }, N { v = 0 }) -> 2
                | (N { v = 0 }, N { v = 100 }) -> 2
                | (N { v = 99 }, N { v = 0 }) -> 1
                | (N { v = 0 }, N { v = 99 }) -> 1
            """;

    private static final String AT_200 = """
                | (N { v = 200 }, N { v = 0 }) -> 3
                | (N { v = 0 }, N { v = 199 }) -> 2
            """;

    /** The points of the threshold 100 answered, and the points of the threshold 200 not. */
    @Test
    void aThresholdNoRowStandsAtIsAGapAndNamesItself() {
        String report = reportOf(table(200) + AT_100);
        assertTrue(report.contains(MISSING_ON), report);
        assertTrue(report.contains(MISSING_OFF), report);
        assertTrue(report.contains("= 200 in gradeOf"), report);
        assertTrue(report.contains("= 199 in gradeOf"), report);
        assertFalse(report.contains("= 100 in gradeOf"), report);
    }

    /** The same rows with the third bound written 2000 pass nothing more. */
    @Test
    void movingTheThirdBoundDoesNotChangeWhatTheRowsAtTheSecondShow() {
        String report = reportOf(table(2000) + AT_100);
        assertTrue(report.contains(MISSING_ON), report);
        assertTrue(report.contains("= 2000 in gradeOf"), report);
    }

    /** Rows at the points of every threshold leave no point of any of them owed. */
    @Test
    void rowsAtEveryThresholdLeaveNothingOwed() {
        String report = reportOf(table(200) + AT_100 + AT_200);
        assertFalse(report.contains(MISSING_ON), report);
        assertFalse(report.contains(MISSING_OFF), report);
    }

    private static final String AVERAGE_OF_THE_PAYABLE = """
            module demo

            data Pay = { amount: Int, days: Int }
                invariant amount >= 0
            data Row = { grade: Int, lowerBound: Int }
            let table: List<Row> = [ Row { grade = 1, lowerBound = 0 },
                                     Row { grade = 2, lowerBound = 100 },
                                     Row { grade = 3, lowerBound = 300 } ]
            let gradeOf (m: Int): Int =
                List.fold((acc, r) -> if r.lowerBound <= m then r.grade else acc, 0, table)
            let payable (records: List<Pay>): List<Pay> =
                List.filter(r -> r.days >= 17, records)
            let average (records: List<Pay>): Int =
                Rational.toInt(DOWN, List.sum(List.map(r -> r.amount, records))
                                     / List.length(records))

            behavior f : (a: Pay, b: Pay, c: Pay) -> Int

            let f (a, b, c) = gradeOf(average(payable([a, b, c])))

            example f
                | (Pay { amount = 100, days = 20 }, Pay { amount = 0, days = 0 },
                   Pay { amount = 0, days = 0 }) -> 2
                | (Pay { amount = 99, days = 20 }, Pay { amount = 0, days = 0 },
                   Pay { amount = 0, days = 0 }) -> 1
            """;

    /**
     * The same bound held against an average over one kept month and over two is one threshold,
     * though the total of two is cut at twice the bound: a row at the bound of either shows where
     * it falls.
     */
    @Test
    void aBoundIsOneThresholdWhateverNumberOfPositionsTheAverageIsOver() {
        String report = reportOf(AVERAGE_OF_THE_PAYABLE);
        // The bounds 100 and 300, each once for the pairs and the three together.
        assertEquals(2, count(report, MISSING_ON + " (comparison@10"), report);
        assertEquals(2, count(report, MISSING_OFF + " (comparison@10"), report);
        // Said in gradeOf, with the place of its line where another line says the same words.
        assertTrue(report.contains("a.amount + b.amount: = 200 in gradeOf")
                && report.matches("(?s).*a\\.amount \\+ b\\.amount \\+ c\\.amount: = 300"
                        + "( \\(line \\d+ of \\d+\\))? in gradeOf.*"), report);
        // And the bound the table holds, which is what a reader changes, beside the total.
        assertTrue(report.contains(", the bound written is 100"), report);
        assertTrue(report.contains(", the bound written is 300"), report);
    }

    private static String tableHeldAgainst(String comparison) {
        return """
                module demo

                data N = { v: Int }
                    invariant v >= 0
                data Row = { grade: Int, lowerBound: Int }
                let table: List<Row> = [ Row { grade = 1, lowerBound = 0 },
                                         Row { grade = 2, lowerBound = 100 },
                                         Row { grade = 3, lowerBound = 200 } ]
                let gradeOf (m: Int): Int =
                    List.fold((acc, r) -> if %s then r.grade else acc, 0, table)

                behavior f : (a: N, b: N) -> Int

                let f (a, b) =
                    gradeOf(a.v + b.v)

                """.formatted(comparison) + AT_100;
    }

    /** A comparison written with its sides the other way round is the same thresholds. */
    @Test
    void theSidesOfTheComparisonAreWrittenEitherWayRound() {
        String bound = reportOf(tableHeldAgainst("r.lowerBound <= m"));
        String reversed = reportOf(tableHeldAgainst("m >= r.lowerBound"));
        assertEquals(count(bound, MISSING_ON), count(reversed, MISSING_ON), reversed);
        assertEquals(count(bound, MISSING_OFF), count(reversed, MISSING_OFF), reversed);
        assertTrue(reversed.contains("= 200 in gradeOf") && !reversed.contains("= 100 in gradeOf"),
                reversed);
    }

    private static final String TWO_CALLS_REACHING_ONE_NUMBER = """
            module demo

            data N = { v: Int }
                invariant v >= 0
            data Row = { grade: Int, lowerBound: Int }
            let table: List<Row> = [ Row { grade = 1, lowerBound = 0 },
                                     Row { grade = 2, lowerBound = 63 },
                                     Row { grade = 3, lowerBound = 126 } ]
            let gradeOf (months: Int, m: Int): Int =
                List.fold((acc, r) -> if r.lowerBound * months <= m then r.grade else acc, 0, table)

            behavior f : (a: N, b: N, c: N) -> Int

            let f (a, b, c) =
                gradeOf(2, a.v + b.v) + gradeOf(1, c.v)

            """;

    /**
     * The bound 63 held twice over against one total and the bound 126 held against another are
     * two thresholds though both come to 126: each is a threshold of its own total.
     */
    @Test
    void aNumberTwoBoundsComeToIsAThresholdOfEachTotal() {
        String report = reportOf(TWO_CALLS_REACHING_ONE_NUMBER);
        assertTrue(report.contains("a.v + b.v: = 126 in gradeOf")
                || report.contains("= 126 in gradeOf"), report);
        assertEquals(2, count(report, "= 126 in gradeOf"), report);
    }

    private static final String TWO_BRANCHES_REACHING_ONE_NUMBER = """
            module demo

            data N = { v: Int }
                invariant v >= 0
            data Row = { grade: Int, lowerBound: Int }
            let table: List<Row> = [ Row { grade = 1, lowerBound = 0 },
                                     Row { grade = 2, lowerBound = 63 },
                                     Row { grade = 3, lowerBound = 126 } ]
            let gradeOf (months: Int, m: Int): Int =
                List.fold((acc, r) -> if r.lowerBound * months <= m then r.grade else acc, 0, table)

            behavior f : (a: N, b: N, useTwo: Bool) -> Int

            let f (a, b, useTwo) =
                if useTwo then gradeOf(2, a.v + b.v) else gradeOf(1, a.v + b.v)

            example f
                | (N { v = 126 }, N { v = 0 }, true) -> 2
                | (N { v = 125 }, N { v = 0 }, true) -> 1
            """;

    /**
     * Rows at the points of the bound 63 held twice over say nothing of the bound 126 held once,
     * though both come to 126 on the same total: the other branch is not run by them.
     */
    @Test
    void anotherBranchsBoundAtTheSameNumberIsStillOwed() {
        String report = reportOf(TWO_BRANCHES_REACHING_ONE_NUMBER);
        // The branch of the bound 63 held twice over is answered at 126 and owes 252; the other
        // branch owes both of its bounds, 63 and the 126 it comes to.
        assertEquals(1, count(report, "= 126 in gradeOf"), report);
        assertEquals(1, count(report, "= 252 in gradeOf"), report);
        assertEquals(1, count(report, "= 63 in gradeOf"), report);
        assertTrue(report.contains("= 126 in gradeOf@15:47"), report);
    }

    /**
     * The runs beside a line are owed once for the comparison, and every computation cut at the
     * line is a reading of them: the run between 126 and 252 of the one and the run above 126 of the
     * other are both read, whichever branch is written first.
     */
    @Test
    void theRunsBesideALineKeepTheReadingOfEveryComputationCutAtIt() {
        String report = reportOf(TWO_BRANCHES_REACHING_ONE_NUMBER);
        // The same model with the branches written the other way round, and its rows with them.
        String swapped = reportOf(TWO_BRANCHES_REACHING_ONE_NUMBER
                .replace("if useTwo then gradeOf(2, a.v + b.v) else gradeOf(1, a.v + b.v)",
                        "if useTwo then gradeOf(1, a.v + b.v) else gradeOf(2, a.v + b.v)")
                .replace(", true) ->", ", false) ->"));
        assertTrue(report.contains("in 126 < a.v + b.v < 252 in gradeOf"), report);
        assertTrue(report.contains("in 126 < a.v + b.v in gradeOf"), report);
        assertEquals(readingsWithoutPlaces(report), readingsWithoutPlaces(swapped), swapped);
    }

    private static List<String> readingsWithoutPlaces(String report) {
        return report.lines().filter(each -> each.contains("· read as"))
                .map(each -> each.replaceAll("@\\d+:\\d+", "")).sorted().toList();
    }

    /** Where a total may be negative, the bound 0 owes its points like any other. */
    @Test
    void theBoundZeroOwesItsPointsWhereTheTotalCanBeBelowIt() {
        String report = reportOf(table(200).replace("    invariant v >= 0\n", "") + AT_100);
        assertTrue(report.contains("= 0 in gradeOf"), report);
        assertTrue(report.contains("= -1 in gradeOf"), report);
    }

    /**
     * The bound 63 held twice over and the bound 126 held once are the bounds of two computations
     * though they are held against one total: each is a threshold of its own.
     */
    @Test
    void aNumberTwoBoundsComeToIsTwoThresholdsOfOneTotal() {
        String report = reportOf(TWO_CALLS_REACHING_ONE_NUMBER
                .replace("gradeOf(1, c.v)", "gradeOf(1, a.v + b.v)"));
        assertEquals(2, count(report, "= 126 in gradeOf"), report);
    }

    /** The same bound read by two calls cut at the same places is one threshold. */
    @Test
    void theCallsCutAtTheSamePlacesShareTheirThresholds() {
        String report = reportOf(TWO_CALLS_REACHING_ONE_NUMBER
                .replace("gradeOf(1, c.v)", "gradeOf(2, a.v + b.v)"));
        assertEquals(1, count(report, "= 126 in gradeOf"), report);
    }

    /** Two points of one line that differ only in the threshold are two obligations in the
     *  document, and a finding names the one it is about. */
    @Test
    void theDocumentTellsTheThresholdsOfOneLineApart() {
        Compilation compilation = measured(table(200) + AT_100);
        JsonNode document = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        List<JsonNode> found = new ArrayList<>();
        collect(document, found);
        List<String> ids = found.stream().map(each -> each.get("obligationId").toString())
                .toList();
        assertEquals(ids.size(), Set.copyOf(ids).size(), () -> "one entry for each: " + ids);
        assertTrue(found.stream().anyMatch(each -> each.get("obligationId").has("threshold")),
                () -> "a point of a threshold says which: " + ids);
    }

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static void collect(JsonNode node, List<JsonNode> out) {
        if (node.isObject() && node.has("disposition") && node.has("knownWritable")
                && node.has("rule") && node.has("obligationId")) {
            out.add(node);
        }
        for (JsonNode child : node) {
            collect(child, out);
        }
    }

    private static long count(String text, String word) {
        return text.lines().filter(each -> each.contains(word)).count();
    }

    /** The rows offered stand at the threshold no row is at, and only there. */
    @Test
    void theRowsOfferedStandAtTheThresholdNoRowIsAt() {
        Compilation compilation = measured(table(200) + AT_100);
        String block = GeneratedRows.of(
                Adequacy.offeredFor(compilation.db(), OfferingRequest.overTheModule("demo")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                compilation.db()).text();
        assertTrue(block.contains("N { v = 200 }"), block);
        assertTrue(block.contains("N { v = 199 }"), block);
        assertFalse(block.contains("N { v = 100 }") || block.contains("N { v = 99 }"), block);
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static String reportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
