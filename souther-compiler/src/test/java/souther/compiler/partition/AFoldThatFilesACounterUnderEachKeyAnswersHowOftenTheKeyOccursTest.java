package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A map a fold builds by filing a counter under the key of each element holds, under a key, what
 * the counter comes to for the elements of that key — so a statement about one of its values is a
 * statement about how often that key occurs among the elements, and a row is composed on each side
 * of it.
 *
 * <p>Read off what the fold does and what its step does, so the same meaning holds however the
 * list of keys is named and wherever the fold is written, and a fold whose step is anything else
 * says nothing of its values.
 */
class AFoldThatFilesACounterUnderEachKeyAnswersHowOftenTheKeyOccursTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** One row offered for {@code popular}: the keys of the list and the threshold. */
    private record Row(List<String> keys, int atLeast) {

        /** What the fold files under each key, in the order the keys first occur. */
        Map<String, Integer> filed(int first, int step) {
            Map<String, Integer> counts = new LinkedHashMap<>();
            for (String each : keys) {
                counts.merge(each, first, (soFar, _) -> soFar + step);
            }
            return counts;
        }

        /** The entries the filter keeps. */
        Map<String, Integer> kept(int first, int step) {
            Map<String, Integer> out = new LinkedHashMap<>();
            filed(first, step).forEach((key, value) -> {
                if (value >= atLeast) {
                    out.put(key, value);
                }
            });
            return out;
        }

        /** The row as the language writes its inputs. */
        String written() {
            return keys.stream().map(each -> "\"" + each + "\"")
                    .toList() + ", " + atLeast;
        }
    }

    private static String modelOf(String step, String closure, String more) {
        return """
                module example.popular

                let countsOf (xs: List<String>): Map<String, Int> =
                    List.fold((acc, x) -> %s, Map.empty, xs)

                behavior popular : (xs: List<String>, atLeast: Int) -> Map<String, Int>

                let popular (xs, atLeast) =
                    Map.filterEntries((_, count) -> %s, countsOf(xs))
                %s""".formatted(step, closure, more);
    }

    private static final String COUNTING = "Map.updateOrInsert(x, 1, n -> n + 1, acc)";

    @Test
    void aLineOnHowOftenAKeyOccursIsOwedOfferedAndThenMet() {
        String examples = """

                example popular
                    | "some" : (["a", "a", "b"], 2) -> [("a", 2)]
                    | "none" : ([], 2) -> []
                """;
        Compilation before = measured(modelOf(COUNTING, "count >= atLeast", examples));
        assertEquals(2, unmetOf(before).size(),
                () -> "the line's two sides are owed: " + report(before));

        List<Row> offered = offeredRows(before);
        assertFalse(offered.isEmpty(), () -> "rows are offered: " + report(before));

        StringBuilder written = new StringBuilder(examples);
        int named = 0;
        for (Row row : offered) {
            written.append("    | \"offered ").append(named++).append("\" : (")
                    .append(row.written()).append(") -> ")
                    .append(entries(row.kept(1, 1))).append("\n");
        }
        Compilation after = measured(modelOf(COUNTING, "count >= atLeast", written.toString()));
        assertEquals(List.of(), unmetOf(after),
                () -> "the rows that were offered meet the line: " + report(after));
    }

    @Test
    void theLineIsOnTheFoldsValueAgainstTheThreshold() {
        List<Row> rows = offeredRows(measured(modelOf(COUNTING, "count >= atLeast", "")));
        assertTrue(rows.stream().anyMatch(row -> top(row.filed(1, 1)) == row.atLeast()),
                () -> "a row whose largest counter is the threshold: " + rows);
        assertTrue(rows.stream().anyMatch(row -> top(row.filed(1, 1)) == row.atLeast() - 1),
                () -> "a row whose largest counter is one short of it: " + rows);
        assertTrue(rows.stream().anyMatch(row -> top(row.filed(1, 1)) > row.atLeast()),
                () -> "a row well past it: " + rows);
        assertTrue(rows.stream().anyMatch(row -> top(row.filed(1, 1)) < row.atLeast() - 1),
                () -> "a row well short of it: " + rows);
    }

    /** What the counter starts at and adds moves where on how often the key occurs the line falls. */
    @Test
    void whatTheFoldStartsAtAndAddsMovesTheLine() {
        record Fold(String step, int first, int add) { }
        for (Fold fold : List.of(
                new Fold("Map.updateOrInsert(x, 0, n -> n + 1, acc)", 0, 1),
                new Fold("Map.updateOrInsert(x, 1, n -> n + 2, acc)", 1, 2),
                new Fold("Map.updateOrInsert(x, 5, n -> 3 + n, acc)", 5, 3),
                new Fold("Map.updateOrInsert(x, 4, n -> n - 1, acc)", 4, -1))) {
            List<Row> rows = offeredRows(measured(modelOf(fold.step(), "count >= atLeast", "")));
            assertFalse(rows.isEmpty(), () -> "rows for " + fold);
            assertTrue(rows.stream().anyMatch(row ->
                            top(row.filed(fold.first(), fold.add())) == row.atLeast()),
                    () -> "a row at the line for " + fold + ": " + rows);
            assertTrue(rows.stream().anyMatch(row ->
                            top(row.filed(fold.first(), fold.add())) > row.atLeast()),
                    () -> "a row past it for " + fold + ": " + rows);
        }
    }

    /** A key with no element has no entry, so no row is offered with a counter at none. */
    @Test
    void aKeyNothingHasIsNoEntryAndTheLineStopsAtOne() {
        Compilation compilation = measured(modelOf(COUNTING, "count >= 1", ""));
        List<Row> rows = offeredRows(compilation);
        assertFalse(rows.isEmpty(), () -> report(compilation));
        assertTrue(rows.stream().noneMatch(row -> row.keys().isEmpty()),
                () -> "an empty list files nothing, so it is no side of the line: " + rows);
        assertTrue(report(compilation).contains("no OFF point is owed"),
                () -> "nothing stands below the first element of a key: " + report(compilation));
    }

    /** An empty list has no entry for a condition on an entry to hold at. */
    @Test
    void anEmptyListIsNoEntryForTheLineToHoldAt() {
        Compilation compilation = measured(modelOf(COUNTING, "count >= atLeast", """

                example popular
                    | "none" : ([], 2) -> []
                """));
        JsonNode border = bordersOf(compilation).getFirst();
        border.path("items").forEach(item -> assertFalse(item.path("hit").asBoolean(),
                () -> "no point of the line is where nothing is filed: " + item));
    }

    /** A counter that never moves holds one figure under every key, and still only under a key. */
    @Test
    void aCounterThatNeverMovesIsNoEntryForAnEmptyList() {
        String never = "Map.updateOrInsert(x, 5, n -> n, acc)";
        Compilation compilation = measured(modelOf(never, "count >= atLeast", """

                example popular
                    | "none" : ([], 5) -> []
                """));
        List<JsonNode> borders = bordersOf(compilation);
        assertFalse(borders.isEmpty(), () -> report(compilation));
        borders.forEach(border -> border.path("items").forEach(item ->
                assertFalse(item.path("hit").asBoolean(),
                        () -> "an empty list files nothing, whatever the figure is: " + item)));
    }

    @Test
    void aConditionHeldTwiceDrawsAnotherLineOnTheSameCount() {
        Compilation compilation = measured(
                modelOf(COUNTING, "count >= atLeast && count < 5", ""));
        assertEquals(2, bordersOf(compilation).size(),
                () -> "a line for each comparison: " + report(compilation));
    }

    /** The same fold, wherever it is written, files the same counters. */
    @Test
    void aFoldWrittenInAnotherNameMeansTheSameCounters() {
        String direct = """
                module example.popular

                let tally (keys: List<String>): Map<String, Int> =
                    List.fold((acc, key) -> Map.updateOrInsert(key, 1, k -> k + 1, acc),
                        Map.empty, keys)

                let selected (keys: List<String>, floor: Int): Map<String, Int> =
                    Map.filterEntries((_, seen) -> seen >= floor, tally(keys))

                behavior popular : (xs: List<String>, atLeast: Int) -> Map<String, Int>

                let popular (xs, atLeast) = selected(xs, atLeast)
                """;
        Compilation another = measured(direct);
        assertEquals(axisOf(measured(modelOf(COUNTING, "count >= atLeast", ""))),
                axisOf(another));
        assertTrue(json(another).contains("multiplicity(xs[*])"), () -> report(another));
    }

    /** The lookup and the filing written out are the operation that does both. */
    @Test
    void aCounterWrittenAsALookupAndAFilingMeansTheSameCounters() {
        String written = modelOf("""
                match Map.get(x, acc) with
                    | None -> Map.insert(x, 1, acc)
                    | Some n -> Map.insert(x, n + 1, acc)""", "count >= atLeast", "");
        Compilation compilation = measured(written);
        assertEquals(axisOf(measured(modelOf(COUNTING, "count >= atLeast", ""))),
                axisOf(compilation), () -> report(compilation));
        assertTrue(json(compilation).contains("multiplicity(xs[*])"), () -> report(compilation));
        assertTrue(offeredRows(compilation).stream().anyMatch(row -> !row.keys().isEmpty()),
                () -> report(compilation));
    }

    /** A lookup that files under another key than the one it looked up is no counter of it. */
    @Test
    void aLookupThatFilesUnderAnotherKeyIsNotACounter() {
        Compilation compilation = measured(modelOf("""
                match Map.get(x, acc) with
                    | None -> Map.insert(x, 1, acc)
                    | Some n -> Map.insert("other", n + 1, acc)""", "count >= atLeast", ""));
        assertTrue(bordersOf(compilation).isEmpty(), () -> report(compilation));
    }

    /** What a fold files that is not a counter says nothing of its values. */
    @Test
    void aFoldThatIsNotACounterIsNotReadAsOne() {
        List<String> steps = List.of(
                // the closure is no step by a constant
                "Map.updateOrInsert(x, 0, n -> 127 - n, acc)",
                // the first figure turns on the element
                "Map.updateOrInsert(x, String.length(x), n -> n + 1, acc)",
                // each element replaces what was there
                "Map.insert(x, 1, acc)",
                // what is filed turns on what came before
                "Map.updateOrInsert(x, Map.size(acc), n -> n + 1, acc)",
                // under a key that turns on what came before
                "Map.updateOrInsert(String.fromInt(Map.size(acc)), 1, n -> n + 1, acc)",
                // another key filed beside the counter
                "Map.insert(\"other\", 9, Map.updateOrInsert(x, 1, n -> n + 1, acc))",
                // a counter filed under one key and nothing carried from the elements before it
                "Map.updateOrInsert(\"all\", 1, n -> n + 1, Map.updateOrInsert(x, 1, n -> n + 1,"
                        + " acc))");
        for (String step : steps) {
            Compilation compilation = measured(modelOf(step, "count >= atLeast", ""));
            assertTrue(bordersOf(compilation).isEmpty(),
                    () -> "no line on how often a key occurs for " + step + ": "
                            + report(compilation));
            assertFalse(json(compilation).contains("multiplicity"),
                    () -> "nothing is said of how often a key occurs for " + step);
        }
    }

    /** A map that starts with something in it has entries no element filed. */
    @Test
    void aFoldFromAMapWithEntriesIsNotReadAsACounter() {
        Compilation compilation = measured("""
                module example.popular

                let countsOf (xs: List<String>): Map<String, Int> =
                    List.fold((acc, x) -> Map.updateOrInsert(x, 1, n -> n + 1, acc),
                        Map.insert("z", 5, Map.empty), xs)

                behavior popular : (xs: List<String>, atLeast: Int) -> Map<String, Int>

                let popular (xs, atLeast) =
                    Map.filterEntries((_, count) -> count >= atLeast, countsOf(xs))
                """);
        assertTrue(bordersOf(compilation).isEmpty(), () -> report(compilation));
    }

    /** Keys the language wraps are keys, and are composed under their wrapper. */
    @Test
    void aWrappedKeyIsComposedUnderItsWrapper() {
        Compilation compilation = measured("""
                module example.popular

                data Label = String

                let countsOf (xs: List<Label>): Map<Label, Int> =
                    List.fold((acc, x) -> Map.updateOrInsert(x, 1, n -> n + 1, acc),
                        Map.empty, xs)

                behavior popular : (xs: List<Label>, atLeast: Int) -> Map<Label, Int>

                let popular (xs, atLeast) =
                    Map.filterEntries((_, count) -> count >= atLeast, countsOf(xs))
                """);
        assertFalse(bordersOf(compilation).isEmpty(), () -> report(compilation));
        List<String> offered = offeredInputs(compilation);
        assertTrue(offered.stream().anyMatch(each -> each.startsWith("[Label(")),
                () -> "the keys are written as the wrapper writes them: " + offered);
    }

    /** A key read at a field of the element is a line still, though no row is chosen for it. */
    @Test
    void aKeyAtAFieldOfTheElementDrawsItsLine() {
        Compilation compilation = measured("""
                module example.popular

                data Item = { label: String, weight: Int }

                let countsOf (xs: List<Item>): Map<String, Int> =
                    List.fold((acc, x) -> Map.updateOrInsert(x.label, 1, n -> n + 1, acc),
                        Map.empty, xs)

                behavior popular : (xs: List<Item>, atLeast: Int) -> Map<String, Int>

                let popular (xs, atLeast) =
                    Map.filterEntries((_, count) -> count >= atLeast, countsOf(xs))
                """);
        List<JsonNode> borders = bordersOf(compilation);
        assertEquals(1, borders.size(), () -> report(compilation));
        assertTrue(json(compilation).contains("multiplicity(xs[*].label)"),
                () -> "how often a label occurs: " + report(compilation));
    }

    private static long top(Map<String, Integer> counters) {
        return counters.values().stream().mapToInt(Integer::intValue).max().orElse(Integer.MIN_VALUE);
    }

    private static String entries(Map<String, Integer> kept) {
        List<String> each = new ArrayList<>();
        kept.forEach((key, value) -> each.add("(\"" + key + "\", " + value + ")"));
        return each.toString();
    }

    /** The points of the lines drawn that no row is at. */
    private static List<String> unmetOf(Compilation compilation) {
        List<String> out = new ArrayList<>();
        unmet(JSON.readTree(json(compilation)), out);
        return out;
    }

    private static void unmet(JsonNode node, List<String> out) {
        if (node.isObject() && "unmet".equals(node.path("disposition").asString())) {
            out.add(node.path("relation").asString());
        }
        node.forEach(child -> unmet(child, out));
    }

    /** The rows the block offers, read back from how they are written. */
    private static List<Row> offeredRows(Compilation compilation) {
        List<Row> out = new ArrayList<>();
        Pattern row = Pattern.compile("^\\[(.*)\\], (-?\\d+)$");
        for (String each : offeredInputs(compilation)) {
            Matcher matched = row.matcher(each);
            if (!matched.matches()) {
                continue;
            }
            List<String> keys = new ArrayList<>();
            Matcher key = Pattern.compile("\"((?:[^\"\\\\]|\\\\.)*)\"").matcher(matched.group(1));
            while (key.find()) {
                keys.add(key.group(1));
            }
            out.add(new Row(keys, Integer.parseInt(matched.group(2))));
        }
        return out;
    }

    private static List<String> offeredInputs(Compilation compilation) {
        return Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("example.popular"))
                .rowsByBehavior().getOrDefault("popular", List.of()).stream()
                .map(row -> String.join(", ",
                        row.inputs().stream().map(FixtureTemplate::text).toList()))
                .toList();
    }

    /** Every border drawn, whichever kind of quantity it is on. */
    private static List<JsonNode> bordersOf(Compilation compilation) {
        List<JsonNode> out = new ArrayList<>();
        collect(JSON.readTree(json(compilation)), out);
        return out;
    }

    private static void collect(JsonNode node, List<JsonNode> out) {
        if (node.isObject() && node.has("items") && node.has("axis")) {
            out.add(node);
        }
        node.forEach(child -> collect(child, out));
    }

    /** The quantity each border is on, as the report names it. */
    private static List<String> axisOf(Compilation compilation) {
        return bordersOf(compilation).stream()
                .map(each -> each.path("axis").asString() + " " + each.path("value").asString())
                .toList();
    }

    private static String json(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** The source measured, which is a source that compiles: a model that did not would have no
     *  line to draw whatever its folds are. */
    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().toString()).toList(),
                () -> "the source compiles: " + source);
        return compilation;
    }
}
