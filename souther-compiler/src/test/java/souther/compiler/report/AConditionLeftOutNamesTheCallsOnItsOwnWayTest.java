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
 * What a search went without names the calls of a helper on the way it searched along, and no
 * call on a way it did not take.
 *
 * <p>The body calls the helper with the same list on two ways that never meet, so the two copies
 * put equal things on their ways. A line inside one of the ways is reached through one call only,
 * and naming the other would send a reader to a call no row that reaches the line goes through.
 */
class AConditionLeftOutNamesTheCallsOnItsOwnWayTest {

    private static final String MODEL = """
            module example.exclusive

            data Line = { a: Int, b: Int }

            behavior f : (xs: List<Line>, flag: Bool, n: Int) -> Int

            let ok (zs: List<Line>): Bool =
                List.sum(List.map(x -> x.a, zs)) + List.sum(List.map(x -> x.a + x.b, zs)) > 0

            let f (xs, flag, n) =
                if flag then (if ok(xs) then (if n < 10 then 1 else 2) else 3)
                else (if ok(xs) then (if n < 20 then 4 else 6) else 5)
            """;

    /**
     * A line on each way, the second read after both copies were made: told by which copy made
     * each entry rather than by what the entry says, it names its own way's call however many
     * copies put an equal entry somewhere before it.
     */
    @Test
    void aLineOnOneWayNamesTheCallOnThatWayAlone() {
        String page = page();
        assertEquals(Set.of(call("if flag then")), callsOnLinesAt(page, "= 10 "),
                "the line inside the first way is reached through that way's call alone");
        assertEquals(Set.of(call("else (")), callsOnLinesAt(page, "= 20 "),
                "and the line inside the second way through that way's call alone");
    }

    private static Set<String> callsOnLinesAt(String page, String point) {
        List<String> lines = page.lines()
                .filter(line -> line.contains("· read as f/n: " + point)).toList();
        assertFalse(lines.isEmpty(), () -> "the line is read at " + point + ": " + page);
        Set<String> out = new LinkedHashSet<>();
        lines.forEach(line -> out.addAll(callsIn(line)));
        return out;
    }

    @Test
    void aRuleOnEachWayNamesTheCallOnThatWay() {
        Set<String> named = new LinkedHashSet<>();
        for (String line : page().lines().filter(line -> line.contains("· not composed against: "))
                .toList()) {
            Set<String> calls = callsIn(line);
            assertEquals(1, calls.size(), () -> "a rule goes down one of the ways: " + line);
            named.addAll(calls);
        }
        assertEquals(Set.of(call("if flag then"), call("else (")), named,
                "and each way's rules name that way's call");
    }

    /** Where the body calls the helper on the line that starts with {@code way}, read off the
     *  model's text. */
    private static String call(String way) {
        List<String> lines = MODEL.lines().toList();
        for (int i = 0; i < lines.size(); i++) {
            if (lines.get(i).strip().startsWith(way)) {
                return "ok@" + (i + 1) + ":" + (lines.get(i).indexOf("ok(") + 1);
            }
        }
        throw new AssertionError("the body has a way written " + way);
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
