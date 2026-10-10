package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison on what {@code Option.withDefault} answers is read as the comparison on the
 * {@code match} the helper is written as.
 *
 * <p>The analysis expands a library operation that nothing states a fact of, so the call and the
 * {@code match} written out are one program to it, and a rule about either draws the same lines.
 */
class AnOptionConsumedByAHelperIsReadAsTheChoiceItIsTest {

    private static String report(String behavior) {
        String source = """
                module m

                data H = { qty: Option<Int>, q: Int }

                %s
                """.formatted(behavior);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String lineAbout(String report, String word) {
        return report.lines().filter(line -> line.contains(word)).findFirst().orElse("");
    }

    @Test
    void aComparisonOnWithDefaultIsReadToTheEnd() {
        String report = report("""
                behavior f : (h: H) -> Bool
                let f (h) = Option.withDefault(0, h.qty) >= 3
                """);

        assertFalse(report.contains("not read"), report);
        assertEquals("complete", measurement(report), report);
    }

    @Test
    void itDrawsTheLinesTheMatchWrittenOutDraws() {
        String called = report("""
                behavior f : (h: H) -> Bool
                let f (h) = Option.withDefault(0, h.qty) >= 3
                """);
        String written = report("""
                behavior f : (h: H) -> Bool
                let f (h) =
                    (match h.qty with
                        | Some v -> v
                        | None -> 0) >= 3
                """);

        assertEquals(lineAbout(written, "border "), lineAbout(called, "border "), called);
        assertEquals(lineAbout(written, "partition "), lineAbout(called, "partition "), called);
    }

    @Test
    void aDefaultAboveTheThresholdKeepsTheNoneSideInTheStatement() {
        String report = report("""
                behavior f : (h: H) -> Bool
                let f (h) = Option.withDefault(5, h.qty) >= 3
                """);

        assertFalse(report.contains("not read"), report);
        assertEquals("complete", measurement(report), report);
    }

    @Test
    void aComparisonAgainstAnotherNumberOfTheInputDrawsALineOnEach() {
        String report = report("""
                behavior f : (h: H) -> Bool
                let f (h) = Option.withDefault(0, h.qty) >= h.q
                """);

        assertEquals("complete", measurement(report), report);
        assertTrue(lineAbout(report, "border ").contains("borders 2"), report);
    }

    @Test
    void theCasesOfASumAreReadAsTheyWere() {
        String report = report("""
                data Small
                data Large
                data Size = Small | Large
                data S = { size: Size, n: Int }

                behavior f : (s: S) -> Bool
                let f (s) =
                    match s.size with
                        | Small -> s.n >= 3
                        | Large -> false
                """);

        assertEquals("complete", measurement(report), report);
        assertTrue(lineAbout(report, "border ").contains("borders 1"), report);
    }

    /**
     * What the helper's own match owes is nothing of the model's.
     *
     * <p>Every point of the line the comparison draws, and the optional absent, are rows here; if
     * reading the helper through put an arm or a rule in the model that nobody wrote, something
     * would be owed that these rows do not answer.
     */
    @Test
    void theRowsTheModelStatesAnswerEverythingTheReadingOwes() {
        Compilation compilation = Compilation.ofSource("""
                module m

                data H = { qty: Option<Int>, q: Int }

                behavior f : (h: H) -> Bool
                let f (h) = Option.withDefault(0, h.qty) >= 3

                example f
                    | "on the line" : (H { qty = 3, q = 0 }) -> true
                    | "off the line" : (H { qty = 2, q = 0 }) -> false
                    | "in" : (H { qty = 10, q = 0 }) -> true
                    | "out" : (H { qty = -4, q = 0 }) -> false
                    | "absent" : (H { qty = None, q = 0 }) -> false
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));

        assertEquals(0, compilation.errors().size(), report);
        assertFalse(report.contains("!"), report);
        assertTrue(report.contains("adequacy: satisfied"), report);
    }

    /**
     * The ways through what the helper does are the helper's and not the body's.
     *
     * <p>The match the helper is written as is read through for what the comparison says of the
     * input, and is no decision the model states: the body has the one rule it has with the call
     * standing, and a row is not owed at the optional's two cases.
     */
    @Test
    void theHelpersOwnMatchIsNoDecisionOfTheModel() {
        String report = report("""
                behavior f : (h: H) -> Bool
                let f (h) = Option.withDefault(5, h.qty) >= 3
                """);

        assertTrue(report.contains("decision    rules 1"), report);
        assertTrue(report.contains("branch      not measured (no row names this behavior)"),
                report);
    }

    /** One that the model writes is a decision of the model, read the way it always was. */
    @Test
    void aMatchTheModelWritesIsStillTwoDecisionRules() {
        String report = report("""
                behavior f : (h: H) -> Bool
                let f (h) =
                    (match h.qty with
                        | Some v -> v
                        | None -> 5) >= 3
                """);

        assertTrue(report.contains("decision    rules 2"), report);
    }

    private static String measurement(String report) {
        String line = lineAbout(report, "measurement:");
        return line.substring(line.indexOf("measurement:") + "measurement:".length()).strip();
    }
}
