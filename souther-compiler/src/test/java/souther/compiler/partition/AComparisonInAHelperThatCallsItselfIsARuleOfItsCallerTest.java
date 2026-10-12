package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison inside a helper that walks a list by calling itself is a rule of the behavior that
 * calls it, about the elements of the list the call hands it.
 *
 * <p>The helper is one method however many calls run it, so its body is read once at each call:
 * the element it takes stands for any element of the list, and the comparison is made on an element
 * only where no element before it ended the walk. {@code go} below returns at the first positive
 * element, so on {@code [1, 0]} it compares the first element and never the second.
 */
class AComparisonInAHelperThatCallsItselfIsARuleOfItsCallerTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String GO = """
            partial let go (xs: List<Int>): List<Int> =
                match List.get(0, xs) with
                    | None -> []
                    | Some x -> if x > 0 then [ x ] else go(List.drop(1, xs))
            """;

    private static final String ONE_LIST = """
            module probe

            data Low
            data High

            HELPERS
            behavior pick : (xs: List<Int>) -> Low | High
            let pick (xs) = if GUARD then High else Low
            """;

    private static final String TWO_LISTS = """
            module probe

            data Low
            data High

            HELPERS
            behavior pick : (a: List<Int>, b: List<Int>) -> Low | High
            let pick (a, b) = if GUARD then High else Low
            """;

    @Test
    void theComparisonIsARuleAboutTheElementsOfTheListTheCallHandsIt() {
        JsonNode report = report(ONE_LIST, GO, "List.length(go(xs)) >= 1", "([1, 0])");
        assertEquals(Set.of("pick/xs[*]"), axes(report),
                () -> "a line on the elements of xs: " + report);
    }

    @Test
    void anElementIsComparedOnlyWhereNoElementBeforeItEndedTheWalk() {
        assertFalse(hitAt(ONE_LIST, GO, "List.length(go(xs)) >= 1", "([1, 0])", "0"),
                "the walk ends at the first element, and the second is never compared");
        assertTrue(hitAt(ONE_LIST, GO, "List.length(go(xs)) >= 1", "([-1, 0])", "0"),
                "the first does not end it, so the second is compared");
    }

    /** A helper spliced into the recursive one is read where the recursive one is. */
    @Test
    void aHelperSplicedIntoItIsReadAtTheSameCall() {
        String helpers = """
                let positive (n: Int): Bool = n > 0

                partial let go (xs: List<Int>): List<Int> =
                    match List.get(0, xs) with
                        | None -> []
                        | Some x -> if positive(x) then [ x ] else go(List.drop(1, xs))
                """;
        JsonNode report = report(ONE_LIST, helpers, "List.length(go(xs)) >= 1", "([1, 0])");
        assertEquals(Set.of("pick/xs[*]"), axes(report),
                () -> "the spliced comparison is about the elements of xs: " + report);
        assertFalse(hitAt(ONE_LIST, helpers, "List.length(go(xs)) >= 1", "([1, 0])", "0"),
                "and is made only on the elements the walk got to");
    }

    /** Two calls on two lists are two rules about two positions. */
    @Test
    void twoCallsOnTwoListsAreReadApart() {
        JsonNode report = report(TWO_LISTS, GO,
                "List.length(go(a)) + List.length(go(b)) >= 1", "([1], [2])");
        assertEquals(Set.of("pick/a[*]", "pick/b[*]"), axes(report),
                () -> "a line on the elements of each list: " + report);
    }

    /**
     * A run recorded in the helper's method is any call's. Where another call ran it, a row whose
     * own call was never made did not meet the line through it, whatever the run recorded.
     */
    @Test
    void aRunRecordedThroughAnotherCallIsNotThisCallsRun() {
        String model = """
                module probe

                data Low
                data High

                HELPERS
                behavior pick : (gate: Bool, a: List<Int>, b: List<Int>) -> Low | High
                let pick (gate, a, b) = if GUARD then High else Low
                """;
        String guard = "if gate then List.length(go(a)) >= 1"
                + " else List.length(go(List.reverse(b))) >= 1";
        assertFalse(hitAt(model, GO, guard, "(false, [0], [1])", "0"),
                "go(a) is never called; the run recorded is the other call's");
        assertTrue(hitAt(model, GO, guard, "(true, [0], [1])", "0"),
                "go(a) is called and compares its element");
    }

    /**
     * Where nothing but one call runs the helper's method, a run recorded there is that call's,
     * however the way to the call is written — even where it is nothing a row's values say.
     */
    @Test
    void aRunRecordedThroughTheOneCallIsThatCallsRun() {
        String model = """
                module probe

                data Low
                data High

                HELPERS
                behavior pick : (s: String, xs: List<Int>) -> Low | High
                let pick (s, xs) = if GUARD then High else Low
                """;
        assertTrue(hitAt(model, GO, "String.startsWith(\"a\", s) && List.length(go(xs)) >= 1",
                        "(\"ab\", [0])", "0"),
                "the one call ran and compared its element");
    }

    /** What ends the walk may be an arm the element takes, and not only a comparison. */
    @Test
    void anArmTheElementTakesMayEndTheWalk() {
        String model = """
                module probe

                data Low
                data High
                data Stop
                data Go = { v: Int }
                data Step = Stop | Go

                partial let go (xs: List<Step>): List<Int> =
                    match List.get(0, xs) with
                        | None -> []
                        | Some x -> match x with
                            | Stop -> []
                            | Go { v } -> if v > 0 then [ v ] else go(List.drop(1, xs))

                behavior pick : (xs: List<Step>) -> Low | High
                let pick (xs) = if List.length(go(xs)) >= 1 then High else Low
                """;
        // The first element is compared either way, so a run is recorded through the comparison
        // on every row here: what tells them apart is which elements it was made on.
        assertFalse(hitAt(model, "", "", "([Go { v = -1 }, Stop, Go { v = 0 }])", "0"),
                "the second element stops the walk, and the third is never compared");
        assertTrue(hitAt(model, "", "", "([Go { v = -1 }, Go { v = -2 }, Go { v = 0 }])", "0"),
                "nothing stops it, so the third is compared");
    }

    private static boolean hitAt(String model, String helpers, String guard, String row,
                                 String against) {
        Map<String, JsonNode> readings = new LinkedHashMap<>();
        JsonNode report = report(model, helpers, guard, row);
        collect(report, readings);
        JsonNode reading = readings.get(against);
        assertTrue(reading != null, () -> "a line has a point at " + against + ": " + readings);
        return reading.path("hit").asBoolean();
    }

    private static Set<String> axes(JsonNode report) {
        Set<String> out = new TreeSet<>();
        axesIn(report, out);
        return out;
    }

    private static void axesIn(JsonNode node, Set<String> out) {
        if (node.isObject() && node.has("against") && node.has("axis")) {
            out.add(node.path("axis").asString());
        }
        node.forEach(child -> axesIn(child, out));
    }

    private static void collect(JsonNode node, Map<String, JsonNode> out) {
        if (node.isObject() && node.has("against") && node.has("hit")) {
            JsonNode before = out.putIfAbsent(node.path("against").asString(), node);
            assertEquals(before == null ? node.path("hit") : before.path("hit"), node.path("hit"),
                    "one point, one answer");
        }
        node.forEach(child -> collect(child, out));
    }

    private static JsonNode report(String model, String helpers, String guard, String row) {
        Compilation compilation = Compilation.ofSource(model.replace("HELPERS", helpers)
                .replace("GUARD", guard) + """

                example pick
                    | "the row" : %s -> High
                """.formatted(row), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
    }
}
