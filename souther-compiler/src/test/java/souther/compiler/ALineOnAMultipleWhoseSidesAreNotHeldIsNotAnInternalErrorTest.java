package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.LinkedHashSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule that writes a multiple of a position is read on the order of the written form, and the
 * values beside its line are then read back in the position's own units. A multiple small enough puts
 * a value beside the line at a whole number with more digits than any number the host builds, which
 * is a fact about the run and not about the values the position has.
 *
 * <p>What is held is the answer and not only that there is one: the line is placed, so the rule is
 * reported as one whose side was not worked out, and never as a line with no place. Compiling it
 * raises nothing, and the measurement of it says so in the document's {@code notRead}.
 *
 * <p>A model whose own example computes the multiple aborts at run time, and that is a diagnostic
 * about the example — the report of the rule is the same.
 */
class ALineOnAMultipleWhoseSidesAreNotHeldIsNotAnInternalErrorTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String THE_SIDE = "line_side_not_worked_out";

    private static final String THE_LINE = "line_at_a_number_no_ratio_holds";

    private static String squarings(int upTo) {
        StringBuilder chain = new StringBuilder("let sq (x: Decimal): Decimal = x * x\n\nlet t0 = 0.1m\n");
        for (int i = 1; i <= upTo; i++) {
            chain.append("let t").append(i).append(" = sq(t").append(i - 1).append(")\n");
        }
        return chain.toString();
    }

    private static String model(String squarings, String body, String example) {
        return """
                module probe.follow

                %s
                data A = Decimal
                data H = { a: A }
                data Ok
                data No
                data Verdict = Ok | No

                behavior take : (h: H) -> Verdict
                let take (h) = { %s }

                %s
                """.formatted(squarings, body, example);
    }

    private static final String EXAMPLE = """
            example take
                | "one" : (H { a = A(50.0m) }) -> No
            """;

    private static final String THE_GUARD = "guard t62 * h.a.value <= 1.0m else Ok\n    No";

    /**
     * The reasons the document of this source names in {@code notRead}, measured as a report is.
     *
     * <p>Compiling reads the rule and measuring reads the values beside its line, which is where a
     * count too wide for the host was written out, so it is the measurement that is asked.
     */
    private static Set<String> notRead(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Set<String> out = new LinkedHashSet<>();
        collect(JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts()))), out);
        return out;
    }

    private static void collect(JsonNode node, Set<String> out) {
        if (node.isObject()) {
            for (String name : node.propertyNames()) {
                if (name.equals("notRead")) {
                    node.get(name).forEach(each -> out.add(each.get("reason").asString()));
                }
                collect(node.get(name), out);
            }
        } else if (node.isArray()) {
            node.forEach(each -> collect(each, out));
        }
    }

    @Test
    void aMultipleWhoseValuesBesideItsLineAreBeyondTheHostIsReportedAsASideNotWorkedOut() {
        String source = model(squarings(62), THE_GUARD, "");

        assertDoesNotThrow(() -> Compiler.compile(source));
        Set<String> words = notRead(source);
        assertTrue(words.contains(THE_SIDE), () -> "the side is what was not worked out: " + words);
        assertFalse(words.contains(THE_LINE), () -> "and the line has a place: " + words);
    }

    /** The example aborts when it runs the multiple, which is its own diagnostic; the rule beside
     *  it is reported the same. */
    @Test
    void anExampleThatRunsTheMultipleIsRefusedAsAnExampleAndTheRuleIsReportedTheSame() {
        String source = model(squarings(62), THE_GUARD, EXAMPLE);

        CompileException refused = assertThrows(CompileException.class,
                () -> Compiler.compile(source));
        assertEquals("E1905", refused.code(), "the example does not hold, and that is all it says");
        assertTrue(notRead(source).contains(THE_SIDE));
    }

    @Test
    void theSameLineAsACondition() {
        String source = model(squarings(62), "if t62 * h.a.value <= 1.0m then Ok else No", "");

        assertDoesNotThrow(() -> Compiler.compile(source));
        assertTrue(notRead(source).contains(THE_SIDE));
    }

    /** The line beside another on one quantity: the two are read through what the first is a
     *  multiple of, in either order. */
    @Test
    void aLineBeyondTheHostWithAnotherOnTheSameQuantityIsReportedAsASideNotWorkedOut() {
        for (String body : new String[] {
                "guard t62 * h.a.value <= 1.0m else Ok\n    guard h.a.value <= 1.0m else Ok\n    No",
                "guard h.a.value <= 1.0m else Ok\n    guard t62 * h.a.value <= 1.0m else Ok\n    No"}) {
            String source = model(squarings(62), body, "");

            assertDoesNotThrow(() -> Compiler.compile(source), body);
            Set<String> words = notRead(source);
            assertTrue(words.contains(THE_SIDE), () -> body + ": " + words);
            assertFalse(words.contains(THE_LINE), () -> body + ": " + words);
        }
    }

    /** A multiple the host has room for reports no side as not worked out, so the words above are
     *  about the multiple and not about every rule that writes one. */
    @Test
    void aMultipleTheHostHasRoomForIsReportedNoSuchWay() {
        String source = model("", "guard 2.0m * h.a.value <= 1.0m else Ok\n    No", "");

        assertDoesNotThrow(() -> Compiler.compile(source));
        Set<String> words = notRead(source);
        assertFalse(words.contains(THE_SIDE), () -> "nothing was left unworked: " + words);
        assertFalse(words.contains(THE_LINE), () -> "and the line has a place: " + words);
    }
}
