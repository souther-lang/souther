package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A count of the elements that meet a quantifier, compared to a number other than zero, where the
 * quantifier says something of a field of one case of an element: the line at that field decides
 * in the case it is at, and what is left of the count beside it is the statements of the other
 * elements, which that case holds as one part.
 */
class ACountBesideALineAtAFieldOfACaseIsReportedTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String CLUES = """
            module k3

            data Is = { n: Int }
            data No = { n: Int }
            data Clue = Is | No

            behavior solve : (clues: List<Clue>) -> Int
            """;

    private static String solve(String quantifier, String count, String no) {
        return CLUES + """
                let solve (clues) =
                    if List.length(List.filter(w -> List.%s(c -> match c with
                                                                 | Is { n } -> %s
                                                                 | No       -> %s, clues), [ 2, 3 ])) %s
                    then 1 else 0

                example solve
                    | "is" : ([ Is { n = 2 } ]) -> 1
                """.formatted(quantifier, quantifier.equals("any") ? "n == w" : "n /= w", no, count);
    }

    @Test
    void exactlyOneOfTwoElementsIsReported() {
        assertReported(solve("any", "== 1", "false"));
    }

    @Test
    void aCaseThatHoldsForEveryElementIsReported() {
        assertReported(solve("any", "== 1", "true"));
    }

    @Test
    void aUniversalQuantifierIsReported() {
        assertReported(solve("all", "== 1", "true"));
    }

    @Test
    void theNeighbouringCountsAreReported() {
        assertReported(solve("any", ">= 1", "false"));
        assertReported(solve("any", "== 2", "false").replace("-> 1", "-> 0"));
    }

    @Test
    void oneElementIsReported() {
        assertReported(solve("any", "== 1", "false").replace("[ 2, 3 ]", "[ 2 ]"));
    }

    @Test
    void aMixOfCasesIsReported() {
        assertReported(solve("any", "== 1", "false").replace(
                "| \"is\" : ([ Is { n = 2 } ]) -> 1",
                "| \"is\" : ([ Is { n = 2 } ]) -> 1\n    | \"both\" : ([ Is { n = 2 }, Is { n = 3 } ]) -> 0\n"
                        + "    | \"mixed\" : ([ Is { n = 2 }, No { n = 3 } ]) -> 1"));
    }

    private static void assertReported(String source) {
        Compilation compilation = ACompiledModel.measured(source, Adequacy.Asked.fullReport());
        JsonNode report = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        assertFalse(report.toString().contains("internal compiler error"),
                () -> "reported without an internal error: " + report);
    }
}
