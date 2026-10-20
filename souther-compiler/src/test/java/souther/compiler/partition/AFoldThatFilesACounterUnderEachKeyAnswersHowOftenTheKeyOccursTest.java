package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import org.opentest4j.AssertionFailedError;

import souther.compiler.DocumentShape;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

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

    /** The line is written in a document the schema shipped beside this accepts. */
    @Test
    void theDocumentNamingHowOftenAKeyOccursIsOneTheSchemaAccepts() {
        DocumentShape.assertShapedLikeTheSchema(JSON.readTree(json(measured(
                modelOf(COUNTING, "count >= atLeast", "")))));
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

    /** The keys {@code xs} holds, as the list the fold is handed is written. */
    private static String modelOver(String keys) {
        return modelOf(COUNTING, "count >= atLeast", "").replace("countsOf(xs))",
                "countsOf(" + keys + "))");
    }

    /**
     * A list a map answered with each element as it is holds the keys of the list it walked, each
     * as often, so it is counted as that list is.
     */
    @Test
    void keysAMapAnsweredAsTheyAreAreCountedAsTheListIs() {
        Compilation plain = measured(modelOf(COUNTING, "count >= atLeast", ""));
        for (String keys : List.of("List.map(k -> k, xs)", "List.map(k -> k, List.map(j -> j, xs))",
                "List.reverse(List.map(k -> k, xs))", "List.map(k -> k, List.sort(xs))")) {
            Compilation compilation = measured(modelOver(keys));
            assertEquals(axisOf(plain), axisOf(compilation),
                    () -> keys + ": " + report(compilation));
            assertTrue(json(compilation).contains("multiplicity(xs[*])"),
                    () -> keys + ": " + report(compilation));
            assertEquals(unreadOf(plain), unreadOf(compilation),
                    () -> keys + ": " + report(compilation));
        }
    }

    /** Whether the map a fold files holds anything, the fold walking {@code keys}. */
    private static String modelOfWhetherItHoldsAnything(String keys) {
        return """
                module example.popular

                let countsOf (xs: List<String>): Map<String, Int> =
                    List.fold((acc, i) -> Map.updateOrInsert(i, 1, n -> n + 1, acc),
                        Map.empty, %s)

                behavior popular : (xs: List<String>) -> Bool

                let popular (xs) = Map.isEmpty(countsOf(xs))
                """.formatted(keys);
    }

    /**
     * A fold walking the elements of a list in another order holds the same keys, each as often, so
     * whether the map it files holds anything is read as it is where the fold walks the list. Which
     * operations reorder is {@code InputPath}'s to say, and is asked there.
     */
    @Test
    void whetherAMapHoldsAnythingIsReadWhateverOrderTheFoldWalksTheKeysIn() {
        Compilation plain = measured(modelOfWhetherItHoldsAnything("xs"));
        assertFalse(axisOf(plain).isEmpty(), () -> report(plain));
        assertSidesAreRead(plain);
        Compilation reversed = measured(modelOfWhetherItHoldsAnything("List.reverse(xs)"));
        assertEquals(axisOf(plain), axisOf(reversed), () -> report(reversed));
        assertEquals(decisionsOf(plain), decisionsOf(reversed), () -> report(reversed));
        assertFalse(report(reversed).contains("not read"), () -> report(reversed));
    }

    /** Each side of a line is read, and neither is read as the other. */
    private static void assertSidesAreRead(Compilation compilation) {
        List<String> decisions = decisionsOf(compilation);
        assertTrue(decisions.stream().anyMatch(each -> each.endsWith(" held")),
                () -> decisions + report(compilation));
        assertTrue(decisions.stream().anyMatch(each -> each.endsWith(" denied")),
                () -> decisions + report(compilation));
        assertTrue(decisions.stream().noneMatch(each -> each.startsWith("not_read")),
                () -> decisions + report(compilation));
    }

    /**
     * A list that kept some of the elements is empty where none of them was kept, which a list
     * that holds something does not say: the map is not read as empty where the list is.
     */
    @Test
    void whetherAMapHoldsAnythingIsNotReadAsHowManyKeysThereAreWhereSomeWereKept() {
        Compilation kept = measured(modelOfWhetherItHoldsAnything(
                "List.filter(k -> String.length(k) > 1, xs)"));
        assertTrue(axisOf(kept).stream().noneMatch(each -> each.contains("List.length(xs)")),
                () -> axisOf(kept) + report(kept));
        assertTrue(decisionsOf(kept).stream()
                        .noneMatch(each -> each.contains("List.length(xs)")),
                () -> decisionsOf(kept) + report(kept));
    }

    /** The rows offered for keys a map answered as they are are the rows offered for the keys. */
    @Test
    void theRowsOfferedForKeysAMapAnsweredAsTheyAreAreTheRowsOfferedForTheKeys() {
        List<Row> plain = offeredRows(measured(modelOf(COUNTING, "count >= atLeast", "")));
        List<Row> offered = offeredRows(measured(modelOver("List.map(k -> k, xs)")));
        assertFalse(offered.isEmpty(), () -> "rows are offered: " + offered);
        assertEquals(plain, offered);
        assertTrue(offered.stream().anyMatch(row -> top(row.filed(1, 1)) == row.atLeast()),
                () -> "a row at the line: " + offered);
    }

    /**
     * A list a map made something else of, or one that kept some of the elements, is not the list
     * it was made from: what is counted in it is not what the keys hold.
     */
    @Test
    void keysAMapChangedOrAFilterKeptAreNotCountedAsTheListIs() {
        for (String keys : List.of(
                "List.map(k -> String.append(k, \"!\"), xs)",
                "List.filter(k -> String.length(k) > 1, xs)",
                "List.map(k -> k, List.filter(k -> String.length(k) > 1, xs))")) {
            Compilation compilation = measured(modelOver(keys));
            assertFalse(json(compilation).contains("multiplicity(xs[*])"),
                    () -> keys + ": " + report(compilation));
        }
    }

    /**
     * Issues with a label inside a detail, folded with the step {@code (acc, k) -> step} over
     * {@code keys}, which is written over {@code issues}.
     */
    private static String modelOfIssues(String step, String keys) {
        return """
                module example.popular

                data Detail = { label: String, weight: Int }

                data Issue = { label: String, detail: Detail, tags: List<String> }

                let countsOf (issues: List<Issue>): Map<String, Int> =
                    List.fold((acc, k) -> %s, Map.empty, %s)

                behavior popular : (issues: List<Issue>, atLeast: Int) -> Map<String, Int>

                let popular (issues, atLeast) =
                    Map.filterEntries((_, count) -> count >= atLeast, countsOf(issues))
                """.formatted(step, keys);
    }

    private static String countedUnder(String key) {
        return "Map.updateOrInsert(" + key + ", 1, n -> n + 1, acc)";
    }

    /**
     * Keys a map took out of each element are the values at that place of the elements, one for
     * each, so how often a key occurs among them is how often it occurs there: the line is the one
     * a fold over the elements draws with the key taken inside the step, however many maps and
     * reorderings stand between.
     */
    @Test
    void keysAMapTookOutOfTheElementsAreCountedAtThePlaceItTookThemFrom() {
        record Taken(String step, String keys, String counted) { }
        // The fold over the issues, one for each place counted.
        Map<String, Compilation> directly = new LinkedHashMap<>();
        for (Taken taken : List.of(
                new Taken(countedUnder("k"), "List.map(i -> i.label, issues)", "label"),
                new Taken(countedUnder("k"), "List.reverse(List.map(i -> i.label, issues))",
                        "label"),
                new Taken(countedUnder("k"), "List.map(i -> i.label, List.reverse(issues))",
                        "label"),
                new Taken(countedUnder("k.label"), "List.map(i -> i.detail, issues)",
                        "detail.label"),
                new Taken(countedUnder("k"),
                        "List.map(d -> d.label, List.map(i -> i.detail, issues))",
                        "detail.label"),
                new Taken(countedUnder("k"),
                        "List.map(d -> d, List.map(i -> { let d = i.detail\n d.label }, issues))",
                        "detail.label"))) {
            Compilation direct = directly.computeIfAbsent(taken.counted(), counted ->
                    measured(modelOfIssues(countedUnder("k." + counted), "issues")));
            Compilation compilation = measured(modelOfIssues(taken.step(), taken.keys()));
            assertEquals(axisOf(direct), axisOf(compilation),
                    () -> taken + ": " + report(compilation));
            assertTrue(json(compilation).contains(
                            "multiplicity(issues[*]." + taken.counted() + ")"),
                    () -> taken + ": " + report(compilation));
            assertEquals(unreadOf(direct), unreadOf(compilation),
                    () -> taken + ": " + report(compilation));
        }
    }

    /**
     * Rows written by hand meet the points of the line on the labels where a fold over the labels
     * the step takes inside meets them: two issues of one label against two stand on the line,
     * against three one short of it, and the third issue's label well short of three. No row is
     * offered for a key at a field, so the meaning of the
     * line is held against what the fold counts on rows written out. The details carry a label
     * of their own, the same for all three, so a count read at that place meets other points.
     */
    @Test
    void rowsWrittenOutMeetTheLineOnTheLabelsAsTheyDoOverTheIssues() {
        String issue = "Issue { label = \"%s\", detail = Detail { label = \"x\", weight = 1 },"
                + " tags = [] }";
        String issues = List.of("a", "a", "b").stream().map(issue::formatted).toList().toString();
        String examples = """

                example popular
                    | "on" : (%s, 2) -> [("a", 2)]
                    | "off" : (%s, 3) -> []
                """.formatted(issues, issues);
        Compilation direct = measured(modelOfIssues(countedUnder("k.label"), "issues")
                + examples);
        Compilation projected = measured(modelOfIssues(countedUnder("k"),
                "List.map(i -> i.label, issues)") + examples);
        assertEquals(3, metOf(direct).stream().filter(Boolean::booleanValue).count(),
                () -> "the rows stand at the ON, OFF and OUT points: " + report(direct));
        assertEquals(metOf(direct), metOf(projected), () -> report(projected));
    }

    /** Whether a row stands at each point of each line drawn, in the order they are drawn. */
    private static List<Boolean> metOf(Compilation compilation) {
        List<Boolean> out = new ArrayList<>();
        bordersOf(compilation).forEach(border -> border.path("items").forEach(item ->
                out.add(item.path("hit").asBoolean())));
        return out;
    }

    /**
     * What a map answered that is no value at a place of the element — something made of one, the
     * same value for every element — and what keeps some elements or answers several for one, are
     * not the values at any place of the elements, each once: nothing is said of how often they
     * occur.
     */
    @Test
    void keysThatAreNoPlaceOfTheElementsEachOnceAreNotCounted() {
        for (String keys : List.of(
                "List.map(i -> String.append(i.label, \"!\"), issues)",
                "List.map(i -> \"same\", issues)",
                "List.map(i -> i.label, List.filter(i -> i.detail.weight > 1, issues))",
                "List.flatMap(i -> i.tags, issues)")) {
            Compilation compilation = measured(modelOfIssues(countedUnder("k"), keys));
            assertFalse(json(compilation).contains("multiplicity("),
                    () -> keys + ": " + report(compilation));
        }
    }

    /**
     * A key read off the element another walk was handed is one key for every element the fold
     * walks: it occurs as often as there are elements, which is no count of a value among them.
     */
    @Test
    void aKeyReadOffAnotherWalksElementIsNotCountedAsTheElementsKey() {
        Compilation compilation = measured("""
                module example.popular

                data Issue = { label: String }

                let under (j: Issue, issues: List<Issue>): Map<String, Int> =
                    List.fold((acc, i) -> Map.updateOrInsert(j.label, 1, n -> n + 1, acc),
                        Map.empty, issues)

                behavior popular : (issues: List<Issue>, atLeast: Int) -> List<Int>

                let popular (issues, atLeast) =
                    List.map(j -> Map.size(Map.filterEntries((_, count) -> count >= atLeast,
                        under(j, issues))), issues)
                """);
        assertFalse(json(compilation).contains("multiplicity("), () -> report(compilation));
    }

    /** A key wrapped in a newtype is the value it wraps under a name, and occurs as often. */
    @Test
    void aKeyWrappedInANewtypeIsCountedAsTheValueItWraps() {
        Compilation compilation = measured("""
                module example.popular

                data Label = String

                data Issue = { label: String }

                let countsOf (issues: List<Issue>): Map<Label, Int> =
                    List.fold((acc, i) -> Map.updateOrInsert(Label(i.label), 1, n -> n + 1, acc),
                        Map.empty, issues)

                behavior popular : (issues: List<Issue>, atLeast: Int) -> Map<Label, Int>

                let popular (issues, atLeast) =
                    Map.filterEntries((_, count) -> count >= atLeast, countsOf(issues))
                """);
        assertTrue(json(compilation).contains("multiplicity(issues[*].label)"),
                () -> report(compilation));
    }

    /**
     * A key read back out of a record the step built is the value the record was given: it occurs
     * as often as that value, whether the field is read off the construction or off a name for it.
     */
    @Test
    void aKeyReadBackOutOfARecordTheStepBuiltIsTheValueItWasGiven() {
        for (String key : List.of("(Key { label = i.label }).label",
                "{ let made = Key { label = i.label }\n made.label }",
                "(Outer { key = Key { label = i.label } }).key.label",
                "{ let made = Outer { key = Key { label = i.label } }\n made.key.label }",
                "{ let made = Shell { outer = Outer { key = Key { label = i.label } } }\n"
                        + " let inner = made.outer.key\n inner.label }")) {
            Compilation compilation = measured("""
                    module example.popular

                    data Issue = { label: String }

                    data Key = { label: String }

                    data Outer = { key: Key }

                    data Shell = { outer: Outer }

                    let countsOf (issues: List<Issue>): Map<String, Int> =
                        List.fold((acc, i) -> Map.updateOrInsert(%s, 1, n -> n + 1, acc),
                            Map.empty, issues)

                    behavior popular : (issues: List<Issue>, atLeast: Int) -> Map<String, Int>

                    let popular (issues, atLeast) =
                        Map.filterEntries((_, count) -> count >= atLeast, countsOf(issues))
                    """.formatted(key));
            assertTrue(json(compilation).contains("multiplicity(issues[*].label)"),
                    () -> key + ": " + report(compilation));
        }
    }

    /**
     * Keys a map wrapped in a newtype, one for each element, are equal exactly where the values they
     * wrap are, so they occur as often as those values do.
     */
    @Test
    void keysAMapWrappedInANewtypeAreCountedAsTheValuesTheyWrap() {
        record Wrapped(String key, String keys) { }
        for (Wrapped wrapped : List.of(
                new Wrapped("k", "List.map(i -> Label(i.label), issues)"),
                new Wrapped("k",
                        "List.reverse(List.map(l -> l, List.map(i -> Label(i.label), issues)))"),
                new Wrapped("k", "List.map(i -> { let l = Label(i.label)\n l }, issues)"),
                new Wrapped("k", "List.map(i -> { let l = Label(i.label)\n let m = l\n m },"
                        + " issues)"),
                new Wrapped("Label(k.label)", "issues"),
                new Wrapped("{ let key = Label(k.label)\n key }", "issues"))) {
            Compilation compilation = measured("""
                    module example.popular

                    data Label = String

                    data Issue = { label: String }

                    let countsOf (issues: List<Issue>): Map<Label, Int> =
                        List.fold((acc, k) -> Map.updateOrInsert(%s, 1, n -> n + 1, acc),
                            Map.empty, %s)

                    behavior popular : (issues: List<Issue>, atLeast: Int) -> Map<Label, Int>

                    let popular (issues, atLeast) =
                        Map.filterEntries((_, count) -> count >= atLeast, countsOf(issues))
                    """.formatted(wrapped.key(), wrapped.keys()));
            assertTrue(json(compilation).contains("multiplicity(issues[*].label)"),
                    () -> wrapped + ": " + report(compilation));
        }
    }

    /**
     * The items of each order are counted in that order: an item each of two orders holds once
     * occurs once in each, which stands one short of a threshold of two and not on it.
     */
    @Test
    void aKeyInEachOfTwoOrdersIsCountedInEachOrderAlone() {
        Compilation compilation = measured("""
                module example.popular

                data Order = { items: List<String> }

                let countsOf (xs: List<String>): Map<String, Int> =
                    List.fold((acc, i) -> Map.updateOrInsert(i, 1, n -> n + 1, acc),
                        Map.empty, xs)

                behavior popular : (orders: List<Order>, atLeast: Int) -> List<Map<String, Int>>

                let popular (orders, atLeast) =
                    List.map(o -> Map.filterEntries((_, count) -> count >= atLeast,
                        countsOf(List.map(i -> i, o.items))), orders)

                example popular
                    | "apart" : ([Order { items = ["a"] }, Order { items = ["a"] }], 2) -> [[], []]
                """);
        assertTrue(json(compilation).contains("multiplicity(orders[*].items[*])"),
                () -> report(compilation));
        assertFalse(hitAt(compilation, "0"), () -> "once in each order is not two: "
                + report(compilation));
        assertTrue(hitAt(compilation, "1"), () -> "it is one short of two: "
                + report(compilation));
    }

    /** Whether a row stands at the point of a line against {@code against}, there being one. */
    private static boolean hitAt(Compilation compilation, String against) {
        List<JsonNode> at = new ArrayList<>();
        bordersOf(compilation).forEach(border -> border.path("items").forEach(item -> {
            if ("=".equals(item.path("relation").asString())
                    && against.equals(item.path("against").asString())) {
                at.add(item);
            }
        }));
        assertFalse(at.isEmpty(), () -> "a point against " + against + ": "
                + bordersOf(compilation));
        return at.stream().anyMatch(item -> item.path("hit").asBoolean());
    }

    /**
     * Keys a map took out of wrapped elements as the values they wrap are those elements: the
     * rows offered are the rows for counting the elements, and written they meet the line.
     */
    @Test
    void keysAMapUnwrappedAreCountedAndTheirRowsMeetTheLine() {
        String model = """
                module example.popular

                data Label = String

                let countsOf (xs: List<Label>): Map<String, Int> =
                    List.fold((acc, x) -> Map.updateOrInsert(x, 1, n -> n + 1, acc),
                        Map.empty, List.map(l -> l.value, xs))

                behavior popular : (xs: List<Label>, atLeast: Int) -> Map<String, Int>

                let popular (xs, atLeast) =
                    Map.filterEntries((_, count) -> count >= atLeast, countsOf(xs))
                %s""";
        String examples = """

                example popular
                    | "some" : ([Label("a"), Label("a"), Label("b")], 2) -> [("a", 2)]
                    | "none" : ([], 2) -> []
                """;
        Compilation before = measured(model.formatted(examples));
        assertTrue(json(before).contains("multiplicity(xs[*])"), () -> report(before));
        assertEquals(2, unmetOf(before).size(),
                () -> "the line's two sides are owed: " + report(before));
        List<Offered> offered = offered(before);
        assertFalse(offered.isEmpty(), () -> "rows are offered: " + report(before));
        StringBuilder written = new StringBuilder(examples);
        int named = 0;
        for (Offered each : offered) {
            written.append("    | \"offered ").append(named++).append("\" : (")
                    .append(each.written()).append(") -> ")
                    .append(entries(each.row().kept(1, 1))).append("\n");
        }
        Compilation after = measured(model.formatted(written));
        assertFalse(bordersOf(after).isEmpty(), () -> report(after));
        assertEquals(List.of(), unmetOf(after),
                () -> "the rows that were offered meet the line: " + report(after));
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

    /**
     * Touches carrying labels of the type {@code labels}, folded over {@code keys}, the list of
     * the labels of all of them, which is written over {@code ts}.
     */
    private static String modelOfTouches(String labels, String keys) {
        return """
                module example.popular

                data Label = String

                data Touch = { labels: %s }

                let labelCounts (ts: List<Touch>): Map<String, Int> =
                    List.fold((acc, k) -> Map.updateOrInsert(k, 1, n -> n + 1, acc),
                        Map.empty, %s)

                behavior popular : (ts: List<Touch>) -> Map<String, Int>

                let popular (ts) =
                    Map.filterEntries((_, count) -> count >= 3, labelCounts(ts))
                """.formatted(labels, keys);
    }

    private static final Pattern TOUCH = Pattern.compile("Touch \\{ labels = \\[([^\\]]*)\\] \\}");

    /** The labels of each touch of an offered row, which is written as its inputs are. */
    private static List<List<String>> touchesIn(String row) {
        List<List<String>> out = new ArrayList<>();
        Matcher touch = TOUCH.matcher(row);
        while (touch.find()) {
            out.add(keysIn(touch.group(1)));
        }
        return out;
    }

    /** How often each label occurs among the labels of all the touches. */
    private static Map<String, Integer> occurrencesAcross(List<List<String>> touches) {
        Map<String, Integer> counts = new LinkedHashMap<>();
        touches.forEach(labels -> labels.forEach(label -> counts.merge(label, 1, Integer::sum)));
        return counts;
    }

    /**
     * The labels of the touches, put end to end, are the keys the fold files a counter under, so a
     * label in several touches is counted across them: the line falls on how often a label occurs
     * among all the labels, and a row is composed on each side of it with the label spread over
     * touches that hold it once each.
     */
    @Test
    void labelsOfSeveralTouchesAreCountedAcrossThem() {
        record Shape(String labels, String keys) { }
        for (Shape shape : List.of(
                new Shape("List<String>", "List.flatMap(t -> t.labels, ts)"),
                new Shape("Set<Label>",
                        "List.flatMap(t -> List.map(l -> l.value, Set.toList(t.labels)), ts)"))) {
            Compilation compilation = measured(modelOfTouches(shape.labels(), shape.keys()));
            assertFalse(report(compilation).contains("not read"),
                    () -> shape + ": " + report(compilation));
            assertTrue(json(compilation).contains("occurrences(ts[*].labels[*])"),
                    () -> shape + ": " + report(compilation));

            // A label held once by each touch, or by a touch more than once: the commonest label
            // is on each side of the line at three however it is spread, and a row of one touch
            // would be a count inside it.
            List<List<List<String>>> rows = offeredInputs(compilation).stream()
                    .map(AFoldThatFilesACounterUnderEachKeyAnswersHowOftenTheKeyOccursTest::touchesIn)
                    .toList();
            assertTrue(rows.stream().anyMatch(row -> mostOften(row) == 3 && row.size() == 3),
                    () -> shape + ": a label on the line in three touches: " + rows);
            assertTrue(rows.stream().anyMatch(row -> mostOften(row) == 2),
                    () -> shape + ": a label one short of it: " + rows);
            assertTrue(rows.stream().anyMatch(row -> mostOften(row) > 3),
                    () -> shape + ": a label past it: " + rows);
        }
    }

    /**
     * Rows written by hand meet the points of the line where a label occurs as often among all
     * the touches' labels: three on the line, two one short of it, well past and well short. The
     * touches of the row on the line hold the label once each beside another label, so a count
     * that took every label as the same would read the row short of the line as being on it.
     */
    @Test
    void rowsWrittenOutMeetTheLineOnHowOftenALabelOccursAcrossTheTouches() {
        String keys = "List.flatMap(t -> t.labels, ts)";
        String examples = """

                example popular
                    | "on" : ([Touch { labels = ["a"] }, Touch { labels = ["a", "b"] },
                        Touch { labels = ["a"] }]) -> [("a", 3)]
                    | "off" : ([Touch { labels = ["a"] }, Touch { labels = ["a", "b"] }]) -> []
                    | "past" : ([Touch { labels = ["a", "a"] }, Touch { labels = ["a", "a"] }])
                        -> [("a", 4)]
                    | "short" : ([Touch { labels = ["a"] }]) -> []
                """;
        Compilation compilation = measured(modelOfTouches("List<String>", keys) + examples);
        assertEquals(List.of(), unmetOf(compilation), () -> report(compilation));
    }

    /**
     * A tuple a map built of each element, with the key read out of a component of it, is the
     * key the map gave that component: counted where it stands in the elements.
     */
    @Test
    void aKeyReadOutOfATupleAMapBuiltIsCountedAtThePlaceItWasGiven() {
        record Walked(String params, String walked, String counted) { }
        for (Walked each : List.of(
                new Walked("xs: List<Item>", "List.map(x -> (x.label, x.weight), xs)",
                        "multiplicity(xs[*].label)"),
                new Walked("ts: List<Touch>",
                        "List.flatMap(t -> List.map(l -> (l, t.weight), t.labels), ts)",
                        "occurrences(ts[*].labels[*])"))) {
            Compilation compilation = measured("""
                    module example.popular

                    data Item = { label: String, weight: Int }

                    data Touch = { labels: List<String>, weight: Int }

                    let counts (%1$s): Map<String, Int> =
                        List.fold((acc, p) -> {
                            let (k, _) = p
                            Map.updateOrInsert(k, 1, n -> n + 1, acc)
                        }, Map.empty, %2$s)

                    behavior popular : (%1$s) -> Map<String, Int>

                    let popular (%3$s) =
                        Map.filterEntries((_, count) -> count >= 3, counts(%3$s))
                    """.formatted(each.params(), each.walked(), each.params().substring(0, 2)));
            assertTrue(json(compilation).contains(each.counted()),
                    () -> each + ": " + report(compilation));
        }
    }

    private static String modelOfKept(String keys, String more) {
        return """
                module example.popular

                let countsOf (xs: List<String>): Map<String, Int> =
                    List.fold((acc, k) -> Map.updateOrInsert(k, 1, n -> n + 1, acc),
                        Map.empty, %s)

                behavior popular : (xs: List<String>) -> Map<String, Int>

                let popular (xs) =
                    Map.filterEntries((_, count) -> count >= 3, countsOf(xs))
                %s""".formatted(keys, more);
    }

    /**
     * A key a filter dropped has no entry, and one it kept is counted among the occurrences it
     * kept: rows written by hand meet the points of the line where the kept keys occur as often,
     * and a key dropped as often as the line asks is no entry at all.
     */
    @Test
    void aKeyIsCountedAmongTheOccurrencesAFilterKeptAndHasNoEntryWhereItWasDropped() {
        String examples = """

                example popular
                    | "on" : (["ab", "ab", "ab"]) -> [("ab", 3)]
                    | "off" : (["ab", "ab", "a", "a", "a"]) -> []
                    | "past" : (["ab", "ab", "ab", "ab"]) -> [("ab", 4)]
                    | "short" : (["ab"]) -> []
                    | "dropped" : (["a", "a", "a"]) -> []
                """;
        Compilation compilation = measured(modelOfKept(
                "List.filter(k -> String.length(k) > 1, xs)", examples));
        assertTrue(json(compilation).contains("occurrences(xs[*] kept by"),
                () -> report(compilation));
        assertEquals(List.of("in", "off", "on", "out"), pointsHitOnTheCount(compilation),
                () -> report(compilation));

        // The key the filter drops, as often as the line asks and nowhere else, is no row on it.
        Compilation onlyDropped = measured(modelOfKept(
                "List.filter(k -> String.length(k) > 1, xs)", """

                example popular
                    | "dropped" : (["a", "a", "a"]) -> []
                    | "short" : (["ab"]) -> []
                """));
        assertEquals(List.of("out"), pointsHitOnTheCount(onlyDropped),
                () -> report(onlyDropped));
    }

    /**
     * What a filter keeps is decided by the element and not by the key: of the elements with one
     * label, the ones past the weight are counted and the rest are not, so a label held twice
     * among the kept is at the count two however often it is held in all.
     */
    @Test
    void theElementsWithOneKeyAreCountedOnlyWhereTheFilterKeptThem() {
        String model = """
                module example.popular

                data Item = { label: String, weight: Int }

                let countsOf (xs: List<Item>): Map<String, Int> =
                    List.fold((acc, k) -> Map.updateOrInsert(k, 1, n -> n + 1, acc), Map.empty,
                        List.map(i -> i.label, List.filter(i -> i.weight > 1, xs)))

                behavior popular : (xs: List<Item>) -> Map<String, Int>

                let popular (xs) =
                    Map.filterEntries((_, count) -> count >= 3, countsOf(xs))

                example popular
                    | "on" : ([Item { label = "a", weight = 2 }, Item { label = "a", weight = 2 },
                        Item { label = "a", weight = 2 }]) -> [("a", 3)]
                    | "off" : ([Item { label = "a", weight = 2 }, Item { label = "a", weight = 2 },
                        Item { label = "a", weight = 1 }, Item { label = "a", weight = 1 }]) -> []
                """;
        Compilation compilation = measured(model);
        assertTrue(json(compilation).contains("occurrences(xs[*].label kept by"),
                () -> report(compilation));
        assertEquals(List.of("off", "on"), pointsHitOnTheCount(compilation),
                () -> report(compilation));
    }

    /**
     * Two keepings of one place are two numbers: what a report names a quantity by says which
     * statement keeps the occurrences, so a line on one is not taken for a line on the other.
     */
    @Test
    void twoFiltersOfOnePlaceAreNamedAsTwoQuantities() {
        String example = """

                example popular
                    | "on" : ([Touch { labels = ["ab"] }, Touch { labels = ["ab"] },
                        Touch { labels = ["ab"] }]) -> [("ab", 3)]
                """;
        List<String> kept = new ArrayList<>();
        for (String longerThan : List.of("0", "1")) {
            Compilation compilation = measured(modelOfTouches("List<String>",
                    "List.filter(k -> String.length(k) > " + longerThan
                            + ", List.flatMap(t -> t.labels, ts))") + example);
            Matcher named = Pattern.compile("\"kept_by\"\\s*:\\s*\"([^\"]*)\"")
                    .matcher(json(compilation));
            assertTrue(named.find(), () -> "a quantity counted among the kept names what keeps"
                    + " them: " + report(compilation));
            kept.add(named.group(1));
        }
        assertEquals(2, new HashSet<>(kept).size(), kept.toString());
    }

    /**
     * A statement on the value a nested count is composed of is put to the value it picks, or the
     * count says it was not composed: a row never writes a value as often as asked that the
     * filter drops.
     */
    @Test
    void aCountAmongKeptValuesIsNotComposedOfValuesTheFilterDrops() {
        Compilation compilation = measured(modelOfTouches("List<String>",
                "List.filter(k -> String.length(k) > 1, List.flatMap(t -> t.labels, ts))"));
        List<List<List<String>>> rows = offeredInputs(compilation).stream()
                .map(AFoldThatFilesACounterUnderEachKeyAnswersHowOftenTheKeyOccursTest::touchesIn)
                .toList();
        assertTrue(rows.stream().noneMatch(row -> mostOften(row) >= 2
                        && occurrencesAcross(row).entrySet().stream()
                                .filter(e -> e.getValue() >= 2).allMatch(e -> e.getKey().length() < 2)),
                () -> "a row repeats only values the filter drops: " + rows);
        assertTrue(report(compilation).contains("to repeat that"), () -> report(compilation));
    }

    /**
     * The same across the lists of an outer list: what a filter keeps of the items of all the
     * touches is decided by the item, so of the items with one label the ones past the weight are
     * counted wherever their touches are, and a light item of the label is not.
     */
    @Test
    void itemsWithOneLabelAreCountedAcrossTheTouchesOnlyWhereTheFilterKeptThem() {
        String model = """
                module example.popular

                data Item = { label: String, weight: Int }

                data Touch = { items: List<Item> }

                let countsOf (ts: List<Touch>): Map<String, Int> =
                    List.fold((acc, k) -> Map.updateOrInsert(k, 1, n -> n + 1, acc), Map.empty,
                        List.map(i -> i.label,
                            List.filter(i -> i.weight > 1, List.flatMap(t -> t.items, ts))))

                behavior popular : (ts: List<Touch>) -> Map<String, Int>

                let popular (ts) =
                    Map.filterEntries((_, count) -> count >= 3, countsOf(ts))

                example popular
                    | "on" : ([Touch { items = [Item { label = "a", weight = 2 }] },
                        Touch { items = [Item { label = "a", weight = 2 }] },
                        Touch { items = [Item { label = "a", weight = 2 }] }]) -> [("a", 3)]
                    | "off" : ([Touch { items = [Item { label = "a", weight = 2 }] },
                        Touch { items = [Item { label = "a", weight = 2 },
                            Item { label = "a", weight = 1 }] },
                        Touch { items = [Item { label = "a", weight = 1 }] }]) -> []
                """;
        Compilation compilation = measured(model);
        assertTrue(json(compilation).contains("occurrences(ts[*].items[*].label kept by"),
                () -> report(compilation));
        assertEquals(List.of("off", "on"), pointsHitOnTheCount(compilation),
                () -> report(compilation));
    }

    /** The points of the line on how often a key occurs among those kept that some row is at. */
    private static List<String> pointsHitOnTheCount(Compilation compilation) {
        return bordersOf(compilation).stream()
                .filter(border -> border.path("axis").asString().contains("occurrences"))
                .flatMap(border -> border.path("items").valueStream())
                .filter(item -> item.path("hit").asBoolean())
                .map(item -> item.path("point").asString()).sorted().toList();
    }

    private static int mostOften(List<List<String>> touches) {
        return occurrencesAcross(touches).values().stream().mapToInt(Integer::intValue).max()
                .orElse(0);
    }

    /**
     * Labels a filter kept are some of the labels, and are counted among those and not among all
     * of them: a label the filter drops is no entry however often the touches hold it, and one it
     * kept is counted across the touches that hold it.
     */
    @Test
    void labelsAFilterKeptAreCountedAcrossTheTouchesAndNotAmongAllTheLabels() {
        String examples = """

                example popular
                    | "on" : ([Touch { labels = ["ab"] }, Touch { labels = ["ab", "a"] },
                        Touch { labels = ["ab"] }]) -> [("ab", 3)]
                    | "off" : ([Touch { labels = ["ab", "a"] }, Touch { labels = ["ab", "a"] },
                        Touch { labels = ["a"] }]) -> []
                    | "past" : ([Touch { labels = ["ab", "ab"] }, Touch { labels = ["ab", "ab"] }])
                        -> [("ab", 4)]
                    | "short" : ([Touch { labels = ["ab"] }]) -> []
                    | "dropped" : ([Touch { labels = ["a"] }, Touch { labels = ["a"] },
                        Touch { labels = ["a"] }]) -> []
                """;
        Compilation compilation = measured(modelOfTouches("List<String>",
                "List.filter(k -> String.length(k) > 1, List.flatMap(t -> t.labels, ts))")
                + examples);
        assertTrue(json(compilation).contains("occurrences(ts[*].labels[*] kept by"),
                () -> report(compilation) + axisOf(compilation));
        assertEquals(List.of("in", "off", "on", "out"), pointsHitOnTheCount(compilation),
                () -> report(compilation));
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

    /**
     * The keys of a row are read to the end of the list: none from an empty one, a string with an
     * escaped quote whole, a label as the string it wears, and anything else, or two keys with
     * nothing between them, as a failure rather than a key left out.
     */
    @Test
    void theKeysOfARowAreReadToTheEndOrNotAtAll() {
        assertEquals(List.of(), keysIn(""));
        assertEquals(List.of("a", "b\\\"c", "d"), keysIn("\"a\", \"b\\\"c\", Label(\"d\")"));
        for (String unread : List.of("\"a\", 3", "\"a\" \"b\"", "\"a\",", "Name(\"a\")")) {
            assertThrows(AssertionFailedError.class, () -> keysIn(unread), unread);
        }
    }

    /** A row the block offers, as it is written and as it is read back. */
    private record Offered(String written, Row row) { }

    private static final Pattern ROW = Pattern.compile("^\\[(.*)\\], (-?\\d+)$");

    /** One key of a list of them, where the last one read left off: a string, or a label wearing
     *  one. */
    private static final Pattern KEY = Pattern.compile(
            "\\G(?:^|, )(?:\"((?:[^\"\\\\]|\\\\.)*)\"|Label\\(\"((?:[^\"\\\\]|\\\\.)*)\"\\))");

    /** Every row the block offers, each read back from how it is written; a row this cannot read
     *  back to its end fails, since a part left unread is one nothing checks. */
    private static List<Offered> offered(Compilation compilation) {
        List<Offered> out = new ArrayList<>();
        for (String each : offeredInputs(compilation)) {
            Matcher matched = ROW.matcher(each);
            if (!matched.matches()) {
                fail("an offered row is one this reads back: " + each);
            }
            out.add(new Offered(each, new Row(keysIn(matched.group(1)),
                    Integer.parseInt(matched.group(2)))));
        }
        return out;
    }

    /** The keys {@code list} writes, one after another to its end, or a failure where something
     *  in it is no key. */
    private static List<String> keysIn(String list) {
        List<String> keys = new ArrayList<>();
        Matcher key = KEY.matcher(list);
        int read = 0;
        while (key.find()) {
            keys.add(key.group(1) != null ? key.group(1) : key.group(2));
            read = key.end();
        }
        if (read != list.length()) {
            fail("the keys of an offered row are read to the end: " + list + " (read to " + read
                    + ")");
        }
        return keys;
    }

    /** The rows the block offers, read back from how they are written. */
    private static List<Row> offeredRows(Compilation compilation) {
        return offered(compilation).stream().map(Offered::row).toList();
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

    /** What each decision of the behavior comes to, with how it was read, in the order drawn. */
    private static List<String> decisionsOf(Compilation compilation) {
        List<String> out = new ArrayList<>();
        decisions(JSON.readTree(json(compilation)), out);
        return out;
    }

    private static void decisions(JsonNode node, List<String> out) {
        if (node.isObject() && node.has("condition") && node.has("outcome")) {
            out.add(node.path("kind").asString() + " " + node.path("condition").asString() + " "
                    + node.path("outcome").asString());
        }
        node.forEach(child -> decisions(child, out));
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

    /** The lines saying a place is not read, each as the report writes it but for where the
     *  comparison stands, which moves with how the keys are spelled. */
    private static List<String> unreadOf(Compilation compilation) {
        return report(compilation).lines().map(String::strip)
                .filter(line -> line.contains("not read"))
                .map(line -> line.replaceAll("comparison@\\S+ ", "comparison "))
                .toList();
    }

    /** The source measured, which is a source that compiles: a model that did not would have no
     *  line to draw whatever its folds are. */
    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code().toString()).toList(),
                () -> "the source compiles: " + source);
        return compilation;
    }
}
