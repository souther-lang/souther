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
        assertTrue(report.contains("a.amount + b.amount: = 200 in gradeOf")
                && report.contains("a.amount + b.amount + c.amount: = 300 in gradeOf"), report);
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
