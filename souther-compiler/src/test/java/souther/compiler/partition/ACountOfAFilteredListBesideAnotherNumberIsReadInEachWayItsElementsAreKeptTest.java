package souther.compiler.partition;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
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

    /** As few elements, each kept by a truth of its own, as make more ways than one condition is
     *  read in. */
    private static final String MANY = many(32 - Integer.numberOfLeadingZeros(
            CompositionBudget.READINGS_OF_ONE_CONDITION.maximum()));

    /** {@code elements} elements, {@code a} and {@code b} in turn, each one more than the last of
     *  its own. */
    private static String many(int elements) {
        List<String> each = new ArrayList<>();
        for (int i = 0; i < elements; i++) {
            each.add((i % 2 == 0 ? "a" : "b") + (i < 2 ? "" : " + " + i / 2));
        }
        return "List.filter(x -> x > 0, [" + String.join(", ", each) + "])";
    }

    /** A helper whose body counts what a filter keeps of the two values it was handed. */
    private static final String HELPER = """
            let cnt (x: Int, y: Int): Int = List.length(List.filter(v -> v > 0, [x, y]))
            """;

    /** Each source measured, once for the class: the tests here read what a measurement says and
     *  none changes it, and several ask the same source. */
    private static final Map<String, Compilation> MEASURED = new HashMap<>();

    /**
     * @param after what the source writes after the behavior: its examples, or a helper it calls
     */
    private static Compilation compiled(String body, String after) {
        return MEASURED.computeIfAbsent(source(body, after), source -> {
            Compilation compilation = Compilation.ofSource(source, "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            assertEquals(List.of(), compilation.errors().stream()
                    .map(each -> each.diagnostic().code()).toList(),
                    "the model under test compiles");
            return compilation;
        });
    }

    /** And given back when the class is done with them: a fork keeps its JVM, so what is held
     *  statically is held for every class after this one. */
    @AfterAll
    static void released() {
        MEASURED.clear();
    }

    private static String source(String body, String after) {
        return """
                module p
                data Ok
                data No
                behavior f : (k: Int, a: Int, b: Int) -> Ok | No
                let f (k, a, b) = {
                %s
                    Ok
                }
                %s""".formatted(body, after);
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

    /**
     * The count and the total of ones over the same list are one quantity, read before any
     * comparison is made of it: so one comparison asks it, and every relation the comparison could
     * hold would ask the same reading again.
     */
    @Test
    void theCountIsReadAsTheSumOfOnesOverTheSameListIs() {
        Set<String> count = linesDrawn(report(guarded("k >= " + COUNT)));
        assertTrue(count.contains("· read as f/k: = 1"), count::toString);
        assertEquals(linesDrawn(report(guarded("k >= " + ONES))), count);
    }

    /**
     * Turned round, or with both sides doubled, a comparison states the same lines and is owed
     * the same points.
     *
     * <p>Asked of a relation that is no relation turned round, at and past its value: an equality
     * reads the same either way, so it could not show a reader that forgot to turn one, and the
     * other two are these two turned.
     */
    @Test
    void theSameComparisonWrittenAnotherWayStatesTheSame() {
        for (Related related : RELATIONS.subList(0, 2)) {
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
     *
     * <p>The relation at its value, past it, and on both sides of it, each written once: which
     * way round it is written is the test above, and asked here again it would ask what that one
     * does of the ways.
     */
    @Test
    void theWaysOfKeepingAreOwedWhatTheSameChoicesWrittenOutAre() {
        String eachKept = "(if a > 0 then 1 else 0) + (if b > 0 then 1 else 0)";
        for (Related related : List.of(RELATIONS.get(0), RELATIONS.get(1), RELATIONS.get(4))) {
            assertOwesTheSame(related.kFirst().formatted(COUNT),
                    related.kFirst().formatted(eachKept), "");
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

    /**
     * A count held against nought, or an emptiness check, of values written out states relations
     * of those values and nothing else: lines the comparison holds across, beside the lines of the
     * filter's statement, as the same choices written out as {@code if}s are. Where those come to
     * the denial of one statement, the relation is still no side of the comparison; so it is for a
     * count left alone against a constant inside the ways of another.
     */
    @Test
    void aCountWhoseStatementsComeToOneDenialIsOwedWhatTheChoicesWrittenOutAre() {
        String one = "List.length(List.filter(v -> v > 0, [a]))";
        String other = "List.length(List.filter(v -> v > 0, [b]))";
        String chosen = "(if a > 0 then 1 else 0)";
        String otherChosen = "(if b > 0 then 1 else 0)";
        for (String comparison : List.of("%s <= 0", "%s < 1", "0 >= %s")) {
            assertOwesTheSame(comparison.formatted(one), comparison.formatted(chosen), "");
        }
        assertOwesTheSame("List.isEmpty(List.filter(v -> v > 0, [a]))", chosen + " <= 0", "");
        assertOwesTheSame("List.length(List.filter(v -> v > 0, [b, b])) == 0",
                otherChosen + " + " + otherChosen + " == 0", "");
        assertOwesTheSame(one + " <= " + other, chosen + " <= " + otherChosen, "");
        assertOwesTheSame(one + " + k * " + other + " >= 1",
                chosen + " + k * " + otherChosen + " >= 1", "");
        // The guard's own line, holding where a is at most nought, and the filter's, holding where
        // it is above.
        assertEquals(Set.of("guard on f/a = 0", "guard off f/a = 1", "guard in f/a in a < 0",
                "guard out f/a in 1 < a", "within on f/a = 1", "within off f/a = 0",
                "within in f/a in 1 < a", "within out f/a in a < 0"),
                owedOfEveryRule(one + " <= 0", ""));
    }

    /**
     * Where a count is held against one, or two of them against one, the statements do not come
     * to one denial and nothing was carried past the comparison before either: what it is owed is
     * still what the choices written out are, rule by rule.
     */
    @Test
    void aCountWhoseStatementsComeToMoreThanOneIsOwedWhatTheChoicesWrittenOutAre() {
        String chosen = "(if a > 0 then 1 else 0)";
        String eachKept = chosen + " + (if b > 0 then 1 else 0)";
        assertOwesTheSame("List.length(List.filter(v -> v > 0, [a])) >= 1", chosen + " >= 1", "");
        assertOwesTheSame("List.length(List.filter(v -> v > 0, [a, b])) >= 1", eachKept + " >= 1",
                "");
        assertOwesTheSame("List.length(List.filter(v -> v > 0, [a, b])) <= 1", eachKept + " <= 1",
                "");
    }

    private static void assertOwesTheSame(String kept, String writtenOut, String after) {
        Compilation compilation = compiled(guarded(kept), after);
        String counted = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        assertFalse(counted.contains("not read"), counted);
        Set<String> owed = owedOfEveryRule(compilation, theGuard(kept, after));
        assertTrue(owed.stream().anyMatch(each -> each.startsWith("guard ")),
                () -> kept + " owes points of the guard's own: " + owed);
        assertEquals(owedOfEveryRule(writtenOut, ""), owed, kept);
    }

    private static Set<String> owedOfEveryRule(String condition, String after) {
        return owedOfEveryRule(compiled(guarded(condition), after), theGuard(condition, after));
    }

    /**
     * Each point the behavior is owed, with each reading of it apart, and whose rule owes it: the
     * guard's own comparison, or one written inside it. The comparisons inside are told apart no
     * further, since the filter's own comparison owes for every element what an {@code if} written
     * for each owes for its one.
     *
     * @param guard the rule of the guard's own comparison, as {@link #theGuard} names it
     */
    private static Set<String> owedOfEveryRule(Compilation compilation, String guard) {
        Set<String> out = new TreeSet<>();
        for (JsonNode each : obligationsOf(compilation)) {
            String whose = guard.equals(each.path("rule").asString()) ? "guard" : "within";
            each.path("readings").forEach(reading -> out.add(whose + " "
                    + each.path("point").asString() + " " + reading.path("axis").asString() + " "
                    + reading.path("relation").asString() + " "
                    + reading.path("against").asString()));
        }
        return out;
    }

    /**
     * The rule of the comparison the guard on {@code condition} is, as a report names it: where
     * the one comparison {@code condition} writes outside every bracket has its operator, or,
     * writing none there, where the call it is starts — {@code List.isEmpty(...)} states a size
     * against nought.
     */
    private static String theGuard(String condition, String after) {
        List<Integer> outside = new ArrayList<>();
        int depth = 0;
        for (int i = 0; i < condition.length(); i++) {
            char c = condition.charAt(i);
            if (c == '(' || c == '[') {
                depth++;
            } else if (c == ')' || c == ']') {
                depth--;
            } else if (depth == 0 && (c == '<' || c == '>' || c == '=')) {
                outside.add(i);
                // `<=`, `>=` and `==` are one operator.
                if (i + 1 < condition.length() && condition.charAt(i + 1) == '=') {
                    i++;
                }
            }
        }
        assertTrue(outside.size() <= 1, () -> condition + " writes at most one comparison"
                + " outside every bracket: " + outside);
        assertTrue(!outside.isEmpty() || condition.endsWith(")"),
                () -> condition + " is a comparison or a call");
        String source = source(guarded(condition), after);
        int at = source.indexOf(guarded(condition)) + guarded(condition).indexOf(condition)
                + (outside.isEmpty() ? 0 : outside.getFirst());
        int line = (int) source.substring(0, at).chars().filter(c -> c == '\n').count() + 1;
        int column = at - source.lastIndexOf('\n', at);
        return "comparison@0:" + line + ":" + column;
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
     *  and the comparison is a line on that count less {@code k}, as it was. Which values of
     *  {@code k} settle it on their own is all it leaves unread, the count not being shown to
     *  reach every value. */
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
        List<String> unread = report.lines().filter(line -> line.contains("not read")).toList();
        assertTrue(unread.stream()
                .allMatch(line -> line.contains("not shown to reach every value here")), report);
        assertEquals(Set.of("k", "xs[*]"), unread.stream()
                .map(line -> line.substring(line.lastIndexOf("about `") + 7, line.length() - 1))
                .collect(Collectors.toSet()), report);
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
        return obligationsOf(compiled(body, after));
    }

    /** Each named by where its rule is written, so one rule's obligations are told from
     *  another's at the same point. */
    private static List<JsonNode> obligationsOf(Compilation compilation) {
        JsonNode report = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
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
