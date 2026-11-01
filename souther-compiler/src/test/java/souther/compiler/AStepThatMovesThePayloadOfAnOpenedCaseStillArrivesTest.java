package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A step along a line that moves the payload of the case an arm opened keeps the value that case,
 * so the rows that tell the lines apart are named the same as for a plain input.
 *
 * <p>The behavior is written twice over the same rows: once with {@code b} an input of its own, and
 * once with {@code b} the payload of {@code Points} opened by a {@code match} arm.
 */
class AStepThatMovesThePayloadOfAnOpenedCaseStillArrivesTest {

    private static final String DECLARATIONS = """
            module m

            data Score = Int
                invariant value >= 0 && value <= 49

            data Points = Int
                invariant value >= 0 && value <= 12

            data Result = Points | Fault
            """;

    private static final String PLAIN = DECLARATIONS + """

            behavior f : (a: Score, b: Points) -> Int

            let f (a, b) =
                if b.value >= 1 then
                    if a.value + b.value > 50 then 1
                    else if a.value + b.value < 50 then 2
                    else 3
                else 0
            """;

    private static final String OPENED = DECLARATIONS + """

            behavior f : (a: Score, r: Result) -> Int

            let f (a, r) =
                match r with
                    | Fault -> 0
                    | Points as b ->
                        if b.value >= 1 then
                            if a.value + b.value > 50 then 1
                            else if a.value + b.value < 50 then 2
                            else 3
                        else 0
            """;

    private static final String PLAIN_ROWS = """

            example f
                | (Score(38), Points(0)) -> 0
                | (Score(39), Points(0)) -> 0
                | (Score(49), Points(0)) -> 0
                | (Score(0), Points(0)) -> 0
                | (Score(0), Points(1)) -> 2
                | (Score(38), Points(1)) -> 2
                | (Score(38), Points(2)) -> 2
                | (Score(39), Points(1)) -> 2
                | (Score(49), Points(1)) -> 3
                | (Score(49), Points(2)) -> 1
                | (Score(40), Points(12)) -> 1
                | (Score(37), Points(12)) -> 2
            """;

    private static final String OPENED_ROWS = """

            example f
                | (Score(10), Fault) -> 0
                | (Score(38), Points(0)) -> 0
                | (Score(39), Points(0)) -> 0
                | (Score(49), Points(0)) -> 0
                | (Score(0), Points(0)) -> 0
                | (Score(0), Points(1)) -> 2
                | (Score(38), Points(1)) -> 2
                | (Score(38), Points(2)) -> 2
                | (Score(39), Points(1)) -> 2
                | (Score(49), Points(1)) -> 3
                | (Score(49), Points(2)) -> 1
                | (Score(40), Points(12)) -> 1
                | (Score(37), Points(12)) -> 2
                | (Score(38), Fault) -> 0
                | (Score(39), Fault) -> 0
                | (Score(49), Fault) -> 0
            """;

    private static final String SETTLING_ROWS = """
                | (Score(39), Points(11)) -> 3
                | (Score(40), Points(9)) -> 2
            """;

    private static String reportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** What the report says no row tells apart, with the opened case's payload under the plain name. */
    private static List<String> whatNoRowTells(String report) {
        return report.lines()
                .filter(line -> line.contains("no row tells"))
                .map(line -> line.replace("r@Points", "b"))
                .toList();
    }

    /** The rows that tell the lines apart are the ones the plain input names. */
    @Test
    void theOpenedCaseNamesTheRowsThePlainInputNames() {
        String plain = reportOf(PLAIN + PLAIN_ROWS);
        String opened = reportOf(OPENED + OPENED_ROWS);
        assertFalse(whatNoRowTells(plain).isEmpty(), plain);
        assertEquals(whatNoRowTells(plain), whatNoRowTells(opened), opened);
        assertFalse(opened.contains("read what this measure went without"), opened);
    }

    /** And writing the rows it names settles it. */
    @Test
    void theRowsItNamesSettleIt() {
        String opened = reportOf(OPENED + OPENED_ROWS + SETTLING_ROWS);
        assertTrue(opened.contains("adequacy: satisfied"), opened);
    }
}
