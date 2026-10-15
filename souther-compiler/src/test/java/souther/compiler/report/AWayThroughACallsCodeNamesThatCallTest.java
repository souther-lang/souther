package souther.compiler.report;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.OnTheWay;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrences;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the way to a line was read off a call of a helper names that call, where what put it on
 * the way stands in the body, which is no call.
 *
 * <p>Two shapes put on the way, at a construct of the body, what was read off a helper's code: a
 * joined condition whose halves stand in two calls, and an arm of a fork over what a call
 * answered. Told by what put it there, each part would be sent to the body's own construct; it is
 * read off the call, and a reader is sent there.
 */
class AWayThroughACallsCodeNamesThatCallTest {

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

    private static final String MATCHED = """
            module example.matched

            data Pos
            data Neg
            data Sign = Pos | Neg

            behavior f : (a: Int, n: Int) -> Int

            let sign (k: Int): Sign = if k > 0 then Pos else Neg

            let f (a, n) = match sign(a) with
                | Pos -> (if n < 10 then 1 else 2)
                | Neg -> 3
            """;

    /**
     * Entering an arm of a fork over what a call of a helper answered states what the helper's own
     * fork decided. The fork that is matched stands in the body, which is no call; what entering
     * its arm puts on the way to a line inside it is read off the helper's call.
     */
    @Test
    void anArmOverWhatACallAnsweredIsReadOffThatCall() {
        Compilation compilation = Compilation.ofSource(MATCHED, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> lines =
                Adequacy.searchedBoundariesOf(compilation.db(), "example.matched");
        assertNotNull(lines, "the model under test compiles");
        int told = 0;
        for (BorderAssessment line : lines.get("f")) {
            for (Map.Entry<OnTheWay, ModelOccurrences> each
                    : line.saidOnTheWay().entries().entrySet()) {
                if (each.getKey() instanceof OnTheWay.TakenIn taken
                        && taken.demand().terms().stream()
                        .anyMatch(term -> term.toString().equals("a"))) {
                    assertEquals(1, each.getValue().inOrder().size(),
                            () -> "read off one copy: " + each);
                    assertTrue(each.getValue().inOrder().getFirst().lineage()
                                    instanceof ExpansionLineage.Expansion made
                                    && made.expanded().saidIn("example.matched").equals("sign"),
                            () -> "and that copy is the call of the helper: " + each);
                    told++;
                }
            }
        }
        assertTrue(told > 0, "a line inside the arm is reached through what the arm states of a");
    }

    private static final String EITHER = """
            module example.either

            behavior f : (n: Int, m: Int) -> Int

            let positive (k: Int): Bool = k > 0

            let f (n, m) = if positive(n) || positive(n) then (if m < 10 then 1 else 2) else 3
            """;

    /**
     * A joined condition whose halves ask alike asks one thing, and what it asks on the way to a
     * line past it is read off both halves' calls: a row past it went through one of them, and
     * either is where a reader looks.
     */
    @Test
    void halvesAskingAlikeOnTheWayToALineNameBothCalls() {
        Compilation compilation = Compilation.ofSource(EITHER, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> lines =
                Adequacy.searchedBoundariesOf(compilation.db(), "example.either");
        assertNotNull(lines, "the model under test compiles");
        int told = 0;
        for (BorderAssessment line : lines.get("f")) {
            // The line the body writes itself, past the whole condition. The helper's own line in
            // its second copy is reached only where the first copy's failed, which is one call.
            if (!line.readAt().stream()
                    .allMatch(copy -> copy.lineage().equals(ExpansionLineage.ORIGINAL))) {
                continue;
            }
            for (Map.Entry<OnTheWay, ModelOccurrences> each
                    : line.saidOnTheWay().entries().entrySet()) {
                if (each.getKey() instanceof OnTheWay.TakenIn taken
                        && taken.demand().terms().stream()
                        .anyMatch(term -> term.toString().equals("n"))) {
                    assertEquals(2, each.getValue().inOrder().size(),
                            () -> "read off both halves' calls: " + each);
                    told++;
                }
            }
        }
        assertTrue(told > 0, "the line past the condition is reached through what it asks of n");
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
