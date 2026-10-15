package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a string chosen by cases is equal to another is whether the string of the case taken
 * is: read in each case, as a comparison of that case's string.
 *
 * <p>The same comparison written with the choice outside it — the case first, then the comparison
 * in each arm — is the control: both are one model, and they are measured alike.
 */
class AStringChosenByCasesIsComparedAsTheCaseTakenTest {

    private static String report(String behavior) {
        Compilation compilation = Compilation.ofSource("""
                module p
                data H = { x: Int, s: String, name: Option<String> }
                behavior f : (h: H) -> Bool
                %s
                """.formatted(behavior), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** The lines read, each once: a line the choice's condition draws is said again under the
     *  comparison read through it, as it is of a number chosen by cases. */
    private static List<String> linesAbout(String report, String word) {
        return report.lines().filter(line -> line.contains(word)).map(String::strip).distinct()
                .sorted().toList();
    }

    private static String decisionLine(String report) {
        return report.lines().filter(line -> line.contains("decision ")).findFirst().orElse("");
    }

    private static void readToTheEnd(String report) {
        assertFalse(report.contains("not read"), report);
        assertTrue(report.contains("measurement: complete"), report);
        assertFalse(report.contains("nothing could show a row can be written"), report);
    }

    @Test
    void twoStringsChosenByACondition() {
        Map<String, String> outsideOf = new LinkedHashMap<>();
        outsideOf.put("(if h.x > 0 then \"a\" else \"b\") == \"a\"",
                "if h.x > 0 then \"a\" == \"a\" else \"b\" == \"a\"");
        outsideOf.put("\"a\" == (if h.x > 0 then \"a\" else \"b\")",
                "if h.x > 0 then \"a\" == \"a\" else \"a\" == \"b\"");
        outsideOf.put("(if h.x > 0 then \"a\" else \"b\") /= \"a\"",
                "if h.x > 0 then \"a\" /= \"a\" else \"b\" /= \"a\"");
        outsideOf.forEach((compared, outside) -> {
            String chosen = report("let f (h) = " + compared);
            String written = report("let f (h) = " + outside);

            readToTheEnd(chosen);
            assertEquals(linesAbout(written, "read as"), linesAbout(chosen, "read as"), chosen);
            assertEquals(decisionLine(written), decisionLine(chosen), chosen);
            assertTrue(chosen.contains("read as f/h.x: = 1"), chosen);
        });
    }

    /** Where both cases answer the same string the comparison is read in each, as the same
     *  comparisons written in the arms are. */
    @Test
    void twoCasesAnsweringOneString() {
        String chosen = report("let f (h) = (if h.x > 0 then \"a\" else \"a\") == \"a\"");
        String written = report("let f (h) = if h.x > 0 then \"a\" == \"a\" else \"a\" == \"a\"");

        readToTheEnd(chosen);
        assertEquals(decisionLine(written), decisionLine(chosen), chosen);
    }

    /** A string the input holds, against the one the case answers. */
    @Test
    void againstAStringTheInputHolds() {
        String report = report("let f (h) = (if h.x > 0 then \"a\" else \"b\") == h.s");

        readToTheEnd(report);
        assertTrue(report.contains("read as f/h.x: = 1"), report);
    }

    /** What an optional the input holds comes to with a default written for when it holds none. */
    @Test
    void anOptionalWithADefault() {
        String through = report("let f (h) = Option.withDefault(\"\", h.name) == \"x\"");
        String written = report("""
                let f (h) =
                    match h.name with
                        | Some n -> n == "x"
                        | None -> "" == "x"
                """);

        readToTheEnd(through);
        assertEquals(linesAbout(written, "read as"), linesAbout(through, "read as"), through);
        assertTrue(decisionLine(through).contains("rules"), through);
    }
}
