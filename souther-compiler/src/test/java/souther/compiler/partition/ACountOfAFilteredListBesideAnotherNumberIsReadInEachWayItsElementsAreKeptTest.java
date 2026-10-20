package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many elements a filter keeps of a list the body wrote out, weighed beside another number, is
 * read once for each way the elements are kept: the count is nought, one or two by which of
 * {@code a} and {@code b} are above nought, and in each way the comparison is a line on {@code k}.
 * A count weighed alone is read as which of the statements hold, and makes no ways.
 */
class ACountOfAFilteredListBesideAnotherNumberIsReadInEachWayItsElementsAreKeptTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String COUNT = "List.length(List.filter(x -> x > 0, [a, b]))";

    private static final String ONES =
            "List.sum(List.map(x -> 1, List.filter(x -> x > 0, [a, b])))";

    /** Eighteen elements, each kept by a truth of its own: more ways than one condition is read
     *  in. */
    private static final String MANY = "List.filter(x -> x > 0, [a, b, a + 1, b + 1, a + 2, b + 2,"
            + " a + 3, b + 3, a + 4, b + 4, a + 5, b + 5, a + 6, b + 6, a + 7, b + 7, a + 8, b + 8])";

    private static Compilation compiled(String body, String examples) {
        Compilation compilation = Compilation.ofSource("""
                module p
                data Ok
                data No
                behavior f : (k: Int, a: Int, b: Int) -> Ok | No
                let f (k, a, b) = {
                %s
                    Ok
                }
                %s""".formatted(body, examples), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        return compilation;
    }

    private static String report(String body) {
        Compilation compilation = compiled(body, "");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String guarded(String condition) {
        return "    guard " + condition + " else No";
    }

    /** What the report draws, each line once. */
    private static Set<String> linesDrawn(String report) {
        return report.lines().filter(line -> line.contains("read as")).map(String::strip)
                .collect(Collectors.toCollection(TreeSet::new));
    }

    /**
     * Every row of {@code a} and {@code b} from minus one to one and {@code k} from minus two to
     * three, which the model answers as the rows say: the borders on {@code k} are at nought, one
     * and two, and a row stands at every point of each that one is owed at.
     */
    @Test
    void everyPointOfTheBordersTheWaysDrawIsReachedByARow() {
        StringBuilder rows = new StringBuilder("example f\n");
        for (int k = -2; k <= 3; k++) {
            for (int a = -1; a <= 1; a++) {
                for (int b = -1; b <= 1; b++) {
                    int kept = (a > 0 ? 1 : 0) + (b > 0 ? 1 : 0);
                    rows.append("    | \"k%d a%d b%d\" : (%d, %d, %d) -> %s\n".formatted(
                            k, a, b, k, a, b, k >= kept ? "Ok" : "No"));
                }
            }
        }
        Compilation compilation = compiled(guarded("k >= " + COUNT), rows.toString());
        JsonNode report = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        List<JsonNode> onK = bordersOn(report, "f/k");
        Set<String> at = new TreeSet<>();
        for (JsonNode border : onK) {
            border.path("items").forEach(item -> {
                if ("on".equals(item.path("point").asString())) {
                    at.add(item.path("against").asString());
                }
                assertTrue(item.has("notOwed") || item.path("hit").asBoolean(),
                        () -> "a row at " + item);
            });
        }
        assertEquals(Set.of("0", "1", "2"), at);
    }

    @Test
    void theCountIsReadAsTheSumOfOnesOverTheSameListIs() {
        for (String comparison : List.of("k >= %s", "k > %s", "k <= %s", "k < %s", "k == %s")) {
            Set<String> count = linesDrawn(report(guarded(comparison.formatted(COUNT))));
            assertTrue(count.contains("· read as f/k: = 1"), () -> comparison + ": " + count);
            assertEquals(linesDrawn(report(guarded(comparison.formatted(ONES)))), count,
                    comparison);
        }
    }

    @Test
    void theSameComparisonWrittenAnotherWayStatesTheSame() {
        Set<String> written = linesDrawn(report(guarded("k >= " + COUNT)));
        assertEquals(written, linesDrawn(report(guarded(COUNT + " <= k"))));
        assertEquals(written, linesDrawn(report(guarded("2 * k >= 2 * " + COUNT))));
    }

    /** {@code List.drop(k, xs)} is empty where {@code k} is at least how many {@code xs} holds:
     *  a count a law weighs, which no call counts. */
    @Test
    void aCountALawWeighsIsReadInEachWayAsACountTheSourceWrote() {
        String report = report(guarded(
                "List.isEmpty(List.drop(k, List.filter(x -> x > 0, [a, b])))"));
        assertFalse(report.contains("not read"), report);
        assertTrue(report.contains("read as f/k: = 2"), report);
    }

    /** The total and the count of one list are given in the same ways: where {@code a} alone is
     *  kept the total is {@code a} and the count one. */
    @Test
    void theTotalAndTheCountOfOneListKeepTheSameElements() {
        Set<String> lines = linesDrawn(report("""
                    let xs = List.filter(x -> x > 0, [a, b])
                    guard k >= List.sum(xs) + List.length(xs) else No"""));
        assertTrue(lines.contains("· read as f/k: = 0"), lines::toString);
        assertTrue(lines.contains("· read as f/k: = a + 1"), lines::toString);
        assertTrue(lines.contains("· read as f/k: = b + 1"), lines::toString);
        assertFalse(lines.contains("· read as f/k: = a + 2"), lines::toString);
        assertFalse(lines.contains("· read as f/k: = 1"), lines::toString);
    }

    /** Two counts against each other are each a count beside another number. */
    @Test
    void twoCountsAgainstEachOtherAreRead() {
        String report = report(guarded(COUNT
                + " >= List.length(List.filter(x -> x > 1, [a, b]))"));
        assertFalse(report.contains("not read"), report);
    }

    /** A count weighed alone is read as which of its statements hold, however many there are:
     *  read in its ways, these would be more than one condition is read in. */
    @Test
    void aCountAloneIsReadAsWhichOfItsStatementsHold() {
        String report = report(guarded("List.length(" + MANY + ") >= 1"));
        assertFalse(report.contains("not read"), report);
    }

    /** And the same where a law weighs it: what {@code List.drop} is handed is a constant, so its
     *  law weighs the count alone. */
    @Test
    void aCountALawWeighsAloneIsReadAsWhichOfItsStatementsHold() {
        String report = report(guarded("List.isEmpty(List.drop(1, " + MANY + "))"));
        assertFalse(report.contains("not read"), report);
    }

    @Test
    void aCountWithMoreWaysThanAreReadStopsAtTheBudget() {
        String report = report(guarded("k >= List.length(" + MANY + ")"));
        assertTrue(report.contains("READINGS_OF_ONE_CONDITION"), report);
    }

    /** A count on both sides comes to nought and is weighed nowhere: only the count left is read
     *  in its ways, and the one cancelled, read in its own, would be more than are read. What its
     *  filter states of each element is still drawn, as the filter still asks it. */
    @Test
    void aCountThatCancelsIsNotReadInItsWays() {
        String cancelled = report(guarded("List.length(" + MANY + ") + " + COUNT
                + " >= List.length(" + MANY + ") + k"));
        assertFalse(cancelled.contains("not read"), cancelled);
        assertEquals(linesOnK(report(guarded(COUNT + " >= k"))), linesOnK(cancelled));
    }

    private static Set<String> linesOnK(String report) {
        return linesDrawn(report).stream().filter(line -> line.contains("f/k:"))
                .collect(Collectors.toCollection(TreeSet::new));
    }

    /**
     * A truth that keeps an element is a choice the comparison's definition writes, as the
     * condition of an {@code if} is: what the comparison is owed under each way of keeping is
     * what it is owed under each arm of the same choices written out, and turning the comparison
     * round changes neither.
     */
    @Test
    void whatTheWaysOfKeepingAreOwedIsWhatTheSameChoicesWrittenOutAre() {
        String written = "(if a > 0 then 1 else 0) + (if b > 0 then 1 else 0)";
        List<String> owed = owedByTheGuard("k >= " + COUNT);
        assertEquals(owedByTheGuard("k >= " + written), owed);
        assertEquals(owed, owedByTheGuard(COUNT + " <= k"));
        assertEquals(owedByTheGuard("k > " + COUNT).size(),
                owedByTheGuard(COUNT + " < k").size());
    }

    /** Each point the guard is owed, with what each reading of it is against, in order. */
    private static List<String> owedByTheGuard(String condition) {
        JsonNode report = JSON.readTree(AdequacyReport.of(compiled(guarded(condition), ""))
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        List<JsonNode> obligations = new ArrayList<>();
        collectObligations(report, obligations);
        Set<Integer> guard = new TreeSet<>();
        for (JsonNode each : obligations) {
            each.path("readings").forEach(reading -> {
                if ("f/k".equals(reading.path("axis").asString())) {
                    guard.add(ruleOf(each));
                }
            });
        }
        assertEquals(1, guard.size(), () -> "one rule reads k: " + guard);
        List<String> out = new ArrayList<>();
        for (JsonNode each : obligations) {
            if (guard.contains(ruleOf(each))) {
                Set<String> readings = new TreeSet<>();
                each.path("readings").forEach(reading -> readings.add(
                        reading.path("axis").asString() + " " + reading.path("relation").asString()
                                + " " + reading.path("against").asString()));
                out.add(each.path("point").asString() + " " + readings);
            }
        }
        out.sort(null);
        return out;
    }

    private static int ruleOf(JsonNode obligation) {
        return obligation.at("/obligationId/line/which/rule/ordinal").asInt();
    }

    private static void collectObligations(JsonNode node, List<JsonNode> out) {
        if (node.isObject() && node.has("obligationId") && node.has("point")) {
            out.add(node);
        }
        node.forEach(child -> collectObligations(child, out));
    }

    private static List<JsonNode> bordersOn(JsonNode report, String axis) {
        List<JsonNode> out = new ArrayList<>();
        collect(report, axis, out);
        assertFalse(out.isEmpty(), () -> "a border on " + axis);
        return out;
    }

    private static void collect(JsonNode node, String axis, List<JsonNode> out) {
        if (node.isObject() && node.has("items") && axis.equals(node.path("axis").asString())) {
            out.add(node);
        }
        node.forEach(child -> collect(child, axis, out));
    }
}
