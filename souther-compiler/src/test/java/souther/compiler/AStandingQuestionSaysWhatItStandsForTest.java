package souther.compiler;

import org.junit.jupiter.api.Test;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A question nothing answered says what it stands for.
 *
 * <p>A rule that raised a question and went unaccounted for used to be printed as the question and
 * the rule alone. An author reading it is told the model asked something and nobody answered, and
 * is left to work out whether what is missing is a capability of this compiler, a rewrite of their
 * own clause, or nothing at all — the three are what a report already promises to tell apart, and
 * the line named none of them.
 *
 * <p>So the reason travels with the question, in the words this document already writes for a
 * position nothing divided. Nothing new is promised: it is the same vocabulary, said of the
 * question rather than of the place.
 */
class AStandingQuestionSaysWhatItStandsForTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static AdequacyReport measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation);
    }

    private static String reportOf(String source) {
        return measured(source).human(SourceNameResolver.identity());
    }

    /** What the document says stopped the one question of {@code source}. */
    private static List<String> stoppedInDocument(String source) {
        JsonNode document =
                JSON.readTree(measured(source).json(SourceNameResolver.identity()));
        JsonNode standing = document.get("modules").get(0).get("behaviors").get(0)
                .get("partition").get("unanswered");
        assertEquals(1, standing.size(), "one question, so one entry: " + standing);
        List<String> out = new ArrayList<>();
        standing.get(0).get("stopped").forEach(each -> out.add(each.asString()));
        return out;
    }

    /** The one line of the report about the rule {@code named}. */
    private static String about(String report, String named) {
        return report.lines()
                .filter(line -> line.contains("not accounted for: " + named))
                .findFirst()
                .orElseThrow(() -> new AssertionError(
                        "no question of " + named + " stands:\n" + report));
    }

    /**
     * A rule admitting values by a pattern, which is what raised this.
     *
     * <p>The reading that turns a clause into a set of values has no word for a pattern and the
     * reading of ends is not asked — the rule places no end — so the question about which values
     * may stand there is one nothing answered. What the report is owed is which of those it is, and
     * the answer is that a form went unread rather than that anything about the model is missing.
     *
     * <p>This is what the report says while nothing reads a pattern. The day something does, the
     * question is answered and the line goes; it is not a line whose wording changes.
     */
    @Test
    void aPatternInvariantSaysThatItsFormWentUnread() {
        String report = reportOf("""
                module probe.regex

                data Number = String
                    invariant String.matches("T[0-9]{13}", value)

                data Held = { n: Number }

                behavior read : (h: Held) -> Ok
                """);

        assertEquals("      · not accounted for: invariant Number #1"
                        + " — which values may stand at h.n:"
                        + " written in a form this compiler does not read",
                about(report, "invariant Number #1"));
    }

    /**
     * Two parts of one clause stopped in two ways, and the line says both.
     *
     * <p>{@code a /= b} relates the position to another, which this reading recognised and has no
     * set of one position's values for; {@code String.matches} is a form it does not take apart.
     * The two are lifted by different work, so an author told only one of them lifts it and finds
     * the question still standing.
     *
     * <p>In the order the author wrote them, which is the whole reason the reasons are a list. A
     * report that sorted them would answer by a precedence nothing in the model decides.
     */
    @Test
    void aQuestionWithTwoCausesSaysBothOfThemInTheOrderTheyAreWritten() {
        assertEquals("      · not accounted for: invariant Pair (both)"
                        + " — which values may stand at p.a:"
                        + " it relates two positions rather than dividing one;"
                        + " written in a form this compiler does not read",
                about(reportOf("""
                        module probe.two

                        data Pair = { a: String, b: String }
                            invariant both = a /= b && String.matches("x+", a)

                        behavior read : (p: Pair) -> Ok
                        """), "invariant Pair (both)"));

        assertEquals("      · not accounted for: invariant Pair (both)"
                        + " — which values may stand at p.a:"
                        + " written in a form this compiler does not read;"
                        + " it relates two positions rather than dividing one",
                about(reportOf("""
                        module probe.two

                        data Pair = { a: String, b: String }
                            invariant both = String.matches("x+", a) && a /= b

                        behavior read : (p: Pair) -> Ok
                        """), "invariant Pair (both)"),
                "and the other way round, since the order is the author's and not a precedence");
    }

    /**
     * Two conjuncts stopped by one limit are one thing to lift, so the line says it once.
     *
     * <p>Both halves of the same rule draw the line on {@code x} and neither was read. What a
     * reader is owed is what to lift, and the two want the same reader written — said twice, an
     * author would be shown their own rule as two things.
     *
     * <p>Which is the projection saying they are one thing and not the report dropping one of them:
     * each reason is put into the words the document promises on its own, and the words are made
     * distinct after that.
     */
    @Test
    void twoConjunctsStoppedByOneLimitAreSaidOnce() {
        String line = about(reportOf("""
                module probe.line

                data N = { x: Int, y: Int }
                    invariant said = x <= 10 * 2 && x <= Int.abs(x)

                behavior read : (n: N) -> Ok
                """), "invariant N (said)");

        assertTrue(line.endsWith(": written in a form this compiler does not read"), line);
        assertEquals(1, line.split("written in a form", -1).length - 1,
                "one limit, said once: " + line);
    }

    /**
     * The document says what the report says, from the same projection.
     *
     * <p>Two surfaces of one adequacy document. A consumer reading the machine-readable one is owed
     * what a person reading the other is told — written from a second walk, the two would answer one
     * question differently and nothing would say which to believe.
     *
     * <p>The order is part of what is published. It is the author's, and the schema says so, so a
     * consumer may read the first entry as the first thing to lift.
     */
    @Test
    void theDocumentSaysWhatTheReportSays() {
        assertEquals(List.of("unsupported_syntax"), stoppedInDocument("""
                module probe.regex

                data Number = String
                    invariant String.matches("T[0-9]{13}", value)

                data Held = { n: Number }

                behavior read : (h: Held) -> Ok
                """));

        assertEquals(List.of("unsupported_partition_shape", "unsupported_syntax"),
                stoppedInDocument("""
                        module probe.two

                        data Pair = { a: String, b: String }
                            invariant both = a /= b && String.matches("x+", a)

                        behavior read : (p: Pair) -> Ok
                        """));

        assertEquals(List.of("unsupported_syntax", "unsupported_partition_shape"),
                stoppedInDocument("""
                        module probe.two

                        data Pair = { a: String, b: String }
                            invariant both = String.matches("x+", a) && a /= b

                        behavior read : (p: Pair) -> Ok
                        """),
                "and the order is the author's here too");
    }
}
