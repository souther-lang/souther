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

    @Test
    void theHelperStandingInsideTheModelAddsNoRuleOfItsOwn() {
        String report = report("""
                behavior f : (h: H) -> Bool
                let f (h) = Option.withDefault(5, h.qty) >= 3

                behavior g : (h: H) -> Bool
                let g (h) = h.q >= 3
                """);

        // A comparison that is read states two decision rules, whichever way it is written.
        assertEquals(2, report.lines().filter(line -> line.contains("decision    rules 2"))
                .count(), report);
    }

    private static String measurement(String report) {
        String line = lineAbout(report, "measurement:");
        return line.substring(line.indexOf("measurement:") + "measurement:".length()).strip();
    }
}
