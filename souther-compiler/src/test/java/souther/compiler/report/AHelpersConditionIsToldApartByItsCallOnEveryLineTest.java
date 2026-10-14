package souther.compiler.report;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A condition a helper writes is told apart by the call of the helper on every line of the page that
 * names it: a line the comparison draws, a rule of it nothing turned into a line, and what a search
 * went without on the way to another line.
 *
 * <p>The helper's comparison is one place in the source, and the body calls the helper twice, over
 * two lists. Each call is its own reading of the comparison and its own condition on the way to the
 * guard after them, and a page that sends a reader to the place alone shows the two as one.
 */
class AHelpersConditionIsToldApartByItsCallOnEveryLineTest {

    private static final String MODEL = """
            module example.numbers

            data Yes = { v: Int }
            data No = { why: Int }

            data Line = { a: Int, b: Int }

            behavior f : (xs: List<Line>, ys: List<Line>, n: Int) -> Yes | No
                constructs Yes
                constructs No

            let ok (zs: List<Line>): Bool =
                List.sum(List.map(x -> x.a, zs)) + List.sum(List.map(x -> x.b, zs)) > 0

            let f (xs, ys, n) = {
                guard ok(xs) else No { why = 0 }
                guard ok(ys) else No { why = 2 }
                guard n < 10 else No { why = 1 }
                Yes { v = 1 }
            }
            """;

    @Test
    void aRuleOfTheHelperNothingTurnedIntoALineNamesTheCallItWasReadAt() {
        List<String> lines = page().lines().filter(line -> line.contains("no line: ")).toList();
        assertFalse(lines.isEmpty(), "the helper's comparison draws no line at either call");
        for (String line : lines) {
            String expected = line.contains("xs[*]") ? call("xs") : call("ys");
            assertEquals(Set.of(expected), callsIn(line),
                    () -> "the call over the list the line is about: " + line);
        }
    }

    @Test
    void aReadingOfTheHelpersLineNamesTheCallItWasReadAt() {
        List<String> lines = page().lines()
                .filter(line -> line.contains("· read as f/List.sum(")).toList();
        assertFalse(lines.isEmpty(), "the helper's comparison is read at both calls");
        for (String line : lines) {
            String reading = line.substring(0, line.indexOf(" — "));
            String expected = reading.contains("xs[*]") ? call("xs") : call("ys");
            assertEquals(Set.of(expected), callsIn(reading),
                    () -> "the reading names the call it was read at: " + line);
        }
    }

    @Test
    void whatTheWayToAnotherLineWentWithoutNamesEveryCallItWasMetAt() {
        List<String> lines = page().lines().filter(line -> line.contains("· read as f/n:"))
                .toList();
        assertFalse(lines.isEmpty(), "the guard after the calls is read");
        for (String line : lines) {
            String left = line.substring(line.indexOf("not every condition on the way"));
            assertEquals(Set.of(call("xs"), call("ys")), callsIn(left),
                    () -> "the condition left out is the helper's at both calls: " + line);
        }
    }

    @Test
    void whatASearchOfARuleWentWithoutNamesEveryCallItWasMetAt() {
        List<String> lines = page().lines()
                .filter(line -> line.contains("· not composed against: ")).toList();
        assertFalse(lines.isEmpty(), "the rules nothing settled went without the helper's"
                + " condition");
        for (String line : lines) {
            assertEquals(Set.of(call("xs"), call("ys")), callsIn(line),
                    () -> "said once, with both calls: " + line);
        }
    }

    /** Where the body calls the helper over {@code list}, as the page writes it, read off the
     *  model's text. */
    private static String call(String list) {
        List<String> lines = MODEL.lines().toList();
        for (int i = 0; i < lines.size(); i++) {
            int at = lines.get(i).indexOf("ok(" + list + ")");
            if (at >= 0) {
                return "ok@" + (i + 1) + ":" + (at + 1);
            }
        }
        throw new AssertionError("the body calls the helper over " + list);
    }

    private static Set<String> callsIn(String text) {
        Set<String> out = new LinkedHashSet<>();
        Matcher call = Pattern.compile("ok@\\d+:\\d+").matcher(text);
        while (call.find()) {
            out.add(call.group());
        }
        return out;
    }

    private static String page() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
