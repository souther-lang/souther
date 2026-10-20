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
import java.util.function.BiPredicate;
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

    /** A helper whose body counts what a filter keeps of the two values it was handed. */
    private static final String HELPER = """
            let cnt (x: Int, y: Int): Int = List.length(List.filter(v -> v > 0, [x, y]))
            """;

    /**
     * @param after what the source writes after the behavior: its examples, or a helper it calls
     */
    private static Compilation compiled(String body, String after) {
        Compilation compilation = Compilation.ofSource("""
                module p
                data Ok
                data No
                behavior f : (k: Int, a: Int, b: Int) -> Ok | No
                let f (k, a, b) = {
                %s
                    Ok
                }
                %s""".formatted(body, after), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        return compilation;
    }

    private static String report(String body) {
        return report(body, "");
    }

    private static String report(String body, String after) {
        Compilation compilation = compiled(body, after);
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

    /** A relation of {@code k} to the count, as written with {@code k} on the left and turned
     *  round, and as it holds of two numbers. */
    private record Related(String kFirst, String countFirst, BiPredicate<Integer, Integer> holds) {}

    private static final List<Related> RELATIONS = List.of(
            new Related("k >= %s", "%s <= k", (k, n) -> k >= n),
            new Related("k > %s", "%s < k", (k, n) -> k > n),
            new Related("k <= %s", "%s >= k", (k, n) -> k <= n),
            new Related("k < %s", "%s > k", (k, n) -> k < n),
            new Related("k == %s", "%s == k", (k, n) -> k.equals(n)));

    /**
     * Every row of {@code a} and {@code b} from minus one to one and {@code k} from minus three to
     * four, which the model answers as the rows say, written either way round: the borders on
     * {@code k} are where the relation turns for a count of nought, one and two, and a row stands
     * at every point of each that one is owed at.
     */
    @Test
    void theBordersAreWhereTheRelationTurnsForEachCountAndARowIsAtEveryPoint() {
        for (Related related : RELATIONS) {
            Set<String> turns = new TreeSet<>();
            StringBuilder rows = new StringBuilder("example f\n");
            for (int k = -3; k <= 4; k++) {
                for (int a = -1; a <= 1; a++) {
                    for (int b = -1; b <= 1; b++) {
                        int kept = (a > 0 ? 1 : 0) + (b > 0 ? 1 : 0);
                        boolean holds = related.holds().test(k, kept);
                        rows.append("    | \"k%d a%d b%d\" : (%d, %d, %d) -> %s\n".formatted(
                                k, a, b, k, a, b, holds ? "Ok" : "No"));
                        if (holds && (related.holds().test(k - 1, kept) != holds
                                || related.holds().test(k + 1, kept) != holds)) {
                            turns.add(String.valueOf(k));
                        }
                    }
                }
            }
            for (String written : List.of(related.kFirst(), related.countFirst())) {
                Compilation compilation = compiled(guarded(written.formatted(COUNT)),
                        rows.toString());
                JsonNode report = JSON.readTree(AdequacyReport.of(compilation)
                        .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
                for (JsonNode border : bordersOn(report, "f/k")) {
                    assertFalse(border.path("items").isEmpty(), () -> written + ": " + border);
                    border.path("items").forEach(item -> assertTrue(
                            item.has("notOwed") || item.path("hit").asBoolean(),
                            () -> written + ": a row at " + item));
                }
                // Where the author's line is, which is what the obligations name; a reading's own
                // border faces the relation it read, turned or not.
                List<JsonNode> obligations = new ArrayList<>();
                collectObligations(report, obligations);
                Set<String> on = new TreeSet<>();
                for (JsonNode each : obligations) {
                    each.path("readings").forEach(reading -> {
                        if ("on".equals(each.path("point").asString())
                                && "f/k".equals(reading.path("axis").asString())) {
                            on.add(reading.path("against").asString());
                        }
                    });
                }
                assertEquals(turns, on, written);
            }
        }
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

    /** Turned round, or with both sides doubled, a comparison states the same lines and is owed
     *  the same points. */
    @Test
    void theSameComparisonWrittenAnotherWayStatesTheSame() {
        for (Related related : RELATIONS) {
            String kFirst = guarded(related.kFirst().formatted(COUNT));
            String countFirst = guarded(related.countFirst().formatted(COUNT));
            Set<String> lines = linesDrawn(report(kFirst));
            List<String> owed = owedByTheGuard(kFirst);
            assertFalse(lines.isEmpty(), related.kFirst());
            assertFalse(owed.isEmpty(), related.kFirst());
            assertEquals(lines, linesDrawn(report(countFirst)), related.kFirst());
            assertEquals(owed, owedByTheGuard(countFirst), related.kFirst());
        }
        assertEquals(linesDrawn(report(guarded("k >= " + COUNT))),
                linesDrawn(report(guarded("2 * k >= 2 * " + COUNT))));
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

    /**
     * What each way of keeping is owed is what the same choices written out as {@code if}s are
     * owed: a relation of {@code k} to the count either way round, a filter handed only what the
     * one inside it kept, the count as a factor of a product, two counts against each other, and
     * a count a helper's body makes, which is written nowhere in the comparison.
     */
    @Test
    void theWaysOfKeepingAreOwedWhatTheSameChoicesWrittenOutAre() {
        String eachKept = "(if a > 0 then 1 else 0) + (if b > 0 then 1 else 0)";
        for (Related related : RELATIONS) {
            for (String written : List.of(related.kFirst(), related.countFirst())) {
                assertOwesTheSame(written.formatted(COUNT), written.formatted(eachKept), "");
            }
        }
        assertOwesTheSame(
                "k >= List.length(List.filter(x -> x > 1, List.filter(x -> x > 0, [a])))",
                "k >= (if a > 0 then (if a > 1 then 1 else 0) else 0)", "");
        assertOwesTheSame("k * " + COUNT + " >= 3", "k * (" + eachKept + ") >= 3", "");
        assertOwesTheSame(COUNT + " > List.length(List.filter(x -> x > 1, [a, b]))",
                eachKept + " > (if a > 1 then 1 else 0) + (if b > 1 then 1 else 0)", "");
        assertOwesTheSame("k * cnt(a, b) >= 3", "k * (" + eachKept + ") >= 3", HELPER);
    }

    /**
     * The one helper's body read for two calls is two counts, each of the values its call handed
     * it: the one the product stops at is read in its ways, and the other, beside {@code k} once
     * the product is a form, in its own.
     */
    @Test
    void aCountIsTheCountOfTheValuesItsCallHandedIt() {
        assertOwesTheSame("k * cnt(a, a) >= cnt(b, b) + k",
                "k * ((if a > 0 then 1 else 0) + (if a > 0 then 1 else 0))"
                        + " >= (if b > 0 then 1 else 0) + (if b > 0 then 1 else 0) + k", HELPER);
    }

    private static void assertOwesTheSame(String kept, String writtenOut, String after) {
        String counted = report(guarded(kept), after);
        assertFalse(counted.contains("not read"), counted);
        Set<String> owed = owedOfEveryRule(guarded(kept), after);
        assertFalse(owed.isEmpty(), kept);
        assertEquals(owedOfEveryRule(guarded(writtenOut), ""), owed, kept);
    }

    /**
     * Each point the behavior is owed, with each reading of it apart, whichever rule owes it: the
     * filter's own comparison owes for every element what an {@code if} written for each owes for
     * its one.
     */
    private static Set<String> owedOfEveryRule(String body, String after) {
        Set<String> out = new TreeSet<>();
        for (JsonNode each : obligationsOf(body, after)) {
            each.path("readings").forEach(reading -> out.add(each.path("point").asString() + " "
                    + reading.path("axis").asString() + " " + reading.path("relation").asString()
                    + " " + reading.path("against").asString()));
        }
        return out;
    }

    /** What a filter keeps by a statement no reader decides stays unread for that statement, and
     *  is not read in ways that would each stop on it. */
    @Test
    void aStatementNoReaderDecidesStopsForItsOwnReason() {
        String report = report(guarded("k >= List.length(List.filter(x -> x * x > 3, [a, b]))"));
        List<String> unread = report.lines().filter(line -> line.contains("not read")).toList();
        assertFalse(unread.isEmpty(), report);
        assertTrue(unread.stream().allMatch(line ->
                        line.contains("a product of two values that are not constants")),
                report);
    }

    /** A list the input holds is no list the body wrote out: its count is a number of its own,
     *  and the comparison is a line on that count less {@code k}, as it was. */
    @Test
    void aCountOfAListTheInputHoldsIsALineOnTheCount() {
        Compilation compilation = Compilation.ofSource("""
                module p
                data Ok
                data No
                behavior f : (k: Int, xs: List<Int>) -> Ok | No
                let f (k, xs) = {
                    guard k >= List.length(List.filter(x -> x > 0, xs)) else No
                    Ok
                }
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        assertTrue(report.contains("read as f/#xs [xs[*] > 0] - k: = 0"), report);
        assertFalse(report.contains("not read"), report);
    }

    /** What the way to the comparison leaves of {@code k} is read before the ways: where it is at
     *  least one, a count of nought or one holds whatever {@code k} is, and only two is a line. */
    @Test
    void whatTheWayHereLeavesIsReadBeforeTheWays() {
        Set<String> lines = linesOnK(report(guarded("k > 0 && k >= " + COUNT)));
        assertEquals(Set.of("· read as f/k: = 1", "· read as f/k: = 2", "· read as f/k: in 2 < k",
                "· read as f/k: = 0", "· read as f/k: in k < 0"), lines);
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

    /** A count beside another number inside a factor is no count a way of keeping makes a form
     *  of: a constant there leaves {@code k * a}, so the product stops for being one, and no way
     *  is read for it. */
    @Test
    void aCountWhoseWaysLeaveTheProductNoFormIsNotReadInThem() {
        String report = report(guarded("k * (a + List.length(" + MANY + ")) >= 3"));
        List<String> unread = report.lines().filter(line -> line.contains("not read")).toList();
        assertFalse(unread.isEmpty(), report);
        assertTrue(unread.stream().allMatch(line ->
                line.contains("a product of two values that are not constants")), report);
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
        Set<String> uncancelled = linesOnK(report(guarded(COUNT + " >= k")));
        assertFalse(uncancelled.isEmpty());
        assertEquals(uncancelled, linesOnK(cancelled));
    }

    private static Set<String> linesOnK(String report) {
        return linesDrawn(report).stream().filter(line -> line.contains("f/k:"))
                .collect(Collectors.toCollection(TreeSet::new));
    }

    /** Each point the guard is owed, with what each reading of it is against, in order. */
    private static List<String> owedByTheGuard(String body) {
        List<JsonNode> obligations = obligationsOf(body, "");
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

    /** Every obligation of the behavior {@code body} writes. */
    private static List<JsonNode> obligationsOf(String body, String after) {
        JsonNode report = JSON.readTree(AdequacyReport.of(compiled(body, after))
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        List<JsonNode> obligations = new ArrayList<>();
        collectObligations(report, obligations);
        return obligations;
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
