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
 * The halves of a joined condition that stand in two calls of a helper are told apart by their
 * calls on the way to a line past it.
 *
 * <p>Both halves are one condition of the body, put on the way at once. Told by the condition, a
 * part read off either call would be sent to the body's own fork, which is no call; each is read
 * off its own half's call, and a reader is sent there.
 */
class TheHalvesOfAJoinedConditionAreToldApartByTheirCallsTest {

    private static final String MODEL = """
            module example.joined

            data Line = { a: Int, b: Int }

            behavior f : (xs: List<Line>, ys: List<Line>, n: Int) -> Int

            let ok (zs: List<Line>): Bool =
                List.sum(List.map(x -> x.a, zs)) + List.sum(List.map(x -> x.b, zs)) > 0

            let f (xs, ys, n) =
                if ok(xs) && ok(ys) then (if n < 10 then 1 else 2) else 3
            """;

    @Test
    void eachHalfLeftOutOnTheWayToTheLineNamesItsOwnCall() {
        String page = page();
        List<String> lines = page.lines().filter(line -> line.contains("· read as f/n:"))
                .toList();
        assertFalse(lines.isEmpty(), () -> "the line past the joined condition is read: " + page);
        Set<String> named = new LinkedHashSet<>();
        for (String line : lines) {
            named.addAll(callsIn(line));
        }
        assertEquals(Set.of(call("ok(xs)"), call("ok(ys)")), named,
                "what the way to the line went without names the call of each half");
    }

    /** Where the body writes {@code written}, as the page names the call. */
    private static String call(String written) {
        List<String> lines = MODEL.lines().toList();
        for (int i = 0; i < lines.size(); i++) {
            int at = lines.get(i).indexOf(written);
            if (at >= 0) {
                return "ok@" + (i + 1) + ":" + (at + 1);
            }
        }
        throw new AssertionError("the body writes " + written);
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
