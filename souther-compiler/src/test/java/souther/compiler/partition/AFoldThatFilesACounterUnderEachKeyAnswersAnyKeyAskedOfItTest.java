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
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * A map a fold builds by filing a counter under the key of each element answers, to a lookup of
 * any key, how often that key occurs among the elements: nothing where it never occurs, and what
 * the counter comes to where it does. A statement about the counter an arm of the lookup opens is
 * a statement about how often the key asked for occurs, and a row is composed on each side of it
 * and of the lookup finding nothing.
 */
class AFoldThatFilesACounterUnderEachKeyAnswersAnyKeyAskedOfItTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** What the fold files under a key: where it starts, what it adds for each occurrence after
     *  the first, and the step that says so. */
    private record Counter(String step, int first, int add) {

        /** What the counter comes to for a key that occurs {@code seen} times. */
        int after(long seen) {
            return (int) (first + (seen - 1) * add);
        }
    }

    private static final Counter COUNTING =
            new Counter("Map.updateOrInsert(k, 1, n -> n + 1, acc)", 1, 1);

    /** One row offered for {@code popular}: the keys of the list and the key asked for, each as
     *  the language writes it. */
    private record Row(List<String> keys, String label) {

        /** How often the key asked for occurs. */
        long occurrences() {
            return keys.stream().filter(label::equals).count();
        }

        /** What {@code popular} answers: the lookup finds nothing where the key never occurs. */
        boolean popular(Counter counter, int atLeast) {
            long seen = occurrences();
            return seen > 0 && counter.after(seen) >= atLeast;
        }

        String written() {
            return keys + ", " + label;
        }
    }

    private static Row ofStrings(List<String> keys, String label) {
        return new Row(keys.stream().map(each -> "\"" + each + "\"").toList(), "\"" + label + "\"");
    }

    private static Row ofInts(List<Integer> keys, int label) {
        return new Row(keys.stream().map(String::valueOf).toList(), String.valueOf(label));
    }

    /** A key type, with the rows the examples that name the behavior are written from: one where
     *  the key occurs and one where nothing does. */
    private record Keys(String type, Row occurs, Row empty) { }

    private static final Keys STRINGS = new Keys("String",
            ofStrings(List.of("a", "a", "a"), "a"), ofStrings(List.of(), "a"));

    private static final Keys INTS = new Keys("Int",
            ofInts(List.of(7, 7, 7), 7), ofInts(List.of(), 7));

    private static String modelOf(Keys keys, Counter counter, int atLeast, String more) {
        return """
                module example.popular

                let countsOf (xs: List<%1$s>): Map<%1$s, Int> =
                    List.fold((acc, k) -> %2$s, Map.empty, xs)

                behavior popular : (xs: List<%1$s>, label: %1$s) -> Bool

                let popular (xs, label) =
                    match Map.get(label, countsOf(xs)) with
                        | Some n -> n >= %3$d
                        | None -> false
                %4$s""".formatted(keys.type(), counter.step(), atLeast, more);
    }

    private static String examples(List<Row> rows, Counter counter, int atLeast) {
        StringBuilder written = new StringBuilder("\nexample popular\n");
        int named = 0;
        for (Row row : rows) {
            written.append("    | \"row ").append(named++).append("\" : (").append(row.written())
                    .append(") -> ").append(row.popular(counter, atLeast)).append("\n");
        }
        return written.toString();
    }

    /**
     * Rows are offered on the line the lookup's counter draws against {@code atLeast}, on both
     * sides of it, and the rows offered meet the line when they are written as examples.
     *
     * <p>Held to the line being there at all: a threshold the counter can never reach, or never
     * fall short of, draws none, and a test of the rows left unmet would pass without it.
     */
    private static void assertTheLineIsOfferedAndMet(Keys keys, Counter counter, int atLeast) {
        List<Boolean> byOccurrences = IntStream.rangeClosed(1, 8).boxed()
                .map(seen -> counter.after(seen) >= atLeast).toList();
        assertTrue(byOccurrences.contains(true) && byOccurrences.contains(false),
                () -> counter + " against " + atLeast + " comes out one way for every count");

        List<Row> seeded = List.of(keys.occurs(), keys.empty());
        Compilation before = measured(modelOf(keys, counter, atLeast,
                examples(seeded, counter, atLeast)));
        assertFalse(unmetOf(before).isEmpty(), () -> "the line is owed: " + report(before));

        List<Row> offered = offeredRows(before);
        List<Row> found = offered.stream().filter(row -> row.occurrences() > 0).toList();
        assertTrue(found.stream().anyMatch(row -> row.popular(counter, atLeast)),
                () -> "a row whose key occurs, on the side of the line it holds: " + offered);
        assertTrue(found.stream().anyMatch(row -> !row.popular(counter, atLeast)),
                () -> "a row whose key occurs, on the side it does not: " + offered);

        List<Row> all = new ArrayList<>(seeded);
        all.addAll(offered);
        Compilation after = measured(modelOf(keys, counter, atLeast,
                examples(all, counter, atLeast)));
        assertEquals(List.of(), unmetOf(after),
                () -> "the rows that were offered meet the line: " + report(after));
    }

    @Test
    void aLineOnHowOftenTheKeyAskedForOccursIsOwedOfferedAndThenMet() {
        assertTheLineIsOfferedAndMet(STRINGS, COUNTING, 3);
    }

    @Test
    void theKeyIsCountedWhateverItsTypeIs() {
        assertTheLineIsOfferedAndMet(INTS, COUNTING, 3);
    }

    @Test
    void theLineIsOnHowOftenTheKeyAskedForOccursAgainstTheThreshold() {
        List<Row> rows = offeredRows(measured(modelOf(STRINGS, COUNTING, 3, "")));
        assertTrue(rows.stream().anyMatch(row -> row.occurrences() == 3),
                () -> "a row whose key occurs at the threshold: " + rows);
        assertTrue(rows.stream().anyMatch(row -> row.occurrences() == 2),
                () -> "a row whose key occurs one short of it: " + rows);
        assertTrue(rows.stream().anyMatch(row -> row.occurrences() > 3),
                () -> "a row whose key occurs past it: " + rows);
        assertTrue(rows.stream().anyMatch(row -> row.occurrences() == 0),
                () -> "a row whose key never occurs: " + rows);
    }

    /** What the counter starts at and adds moves where on how often the key occurs the line
     *  falls, whichever way it adds. */
    @Test
    void whatTheCounterStartsAtAndAddsMovesTheLine() {
        assertTheLineIsOfferedAndMet(STRINGS,
                new Counter("Map.updateOrInsert(k, 2, n -> n + 3, acc)", 2, 3), 6);
        assertTheLineIsOfferedAndMet(STRINGS,
                new Counter("Map.updateOrInsert(k, 5, n -> n - 1, acc)", 5, -1), 3);
    }

    /** A key that occurs among others, in a list that is not empty, is a lookup finding nothing
     *  that is not an empty list answering so. */
    @Test
    void aKeyThatOccursInNoElementOfAListThatHasSomeFindsNothing() {
        Row absent = ofStrings(List.of("a", "a", "b"), "c");
        assertEquals(0, absent.occurrences());
        Compilation compilation = measured(modelOf(STRINGS, COUNTING, 3,
                examples(List.of(STRINGS.occurs(), absent), COUNTING, 3)));
        assertFalse(report(compilation).contains("`case None`"),
                () -> "the one row that finds nothing takes that arm: " + report(compilation));
    }

    /** A key on no order is counted as the same value, which no row is composed for: the line is
     *  read and a row is not said to be impossible. */
    @Test
    void aKeyOnNoOrderIsCountedAsTheSameValueAndNoRowIsSaidImpossible() {
        String report = report(measured("""
                module example.popular

                data Pair = { a: Int, b: Int }

                let countsOf (xs: List<Pair>): Map<Pair, Int> =
                    List.fold((acc, k) -> Map.updateOrInsert(k, 1, n -> n + 1, acc), Map.empty, xs)

                behavior popular : (xs: List<Pair>, label: Pair) -> Bool

                let popular (xs, label) =
                    match Map.get(label, countsOf(xs)) with
                        | Some n -> n >= 3
                        | None -> false
                """));
        assertTrue(report.contains("#xs [xs[*] == label]"), () -> report);
        assertTrue(report.contains("nothing could show a row can be written"), () -> report);
    }

    /** Two lookups of different keys are two counts, and of one key the same one. */
    @Test
    void lookupsOfDifferentKeysAreDifferentCounts() {
        String report = report(measured("""
                module example.popular

                let countsOf (xs: List<String>): Map<String, Int> =
                    List.fold((acc, k) -> Map.updateOrInsert(k, 1, n -> n + 1, acc), Map.empty, xs)

                behavior bothOften : (xs: List<String>, one: String, other: String) -> Bool

                let bothOften (xs, one, other) =
                    match Map.get(one, countsOf(xs)) with
                        | Some n ->
                            match Map.get(other, countsOf(xs)) with
                                | Some m -> n >= 3 && m >= 3
                                | None -> false
                        | None -> false
                """));
        assertTrue(report.contains("#xs [one - xs[*] == 0]")
                && report.contains("#xs [other - xs[*] == 0]"), () -> report);
    }

    /**
     * The list a fold walks may be a position's elements kept by a statement, or a tuple or a
     * record a map built of each, or a map of the kept elements: the key asked for occurs among
     * the elements meeting what they were kept by, and the key of an element is the place it was
     * given. The line is drawn on that count, and the lookup finding nothing is told apart from it
     * as before.
     */
    @Test
    void theElementsAFoldWalksAreThosePutToItInsteadOfThePositionsOwn() {
        record Walked(String walked, String step, String statement) { }
        String record = "Map.updateOrInsert(p.label, 1, n -> n + 1, acc)";
        String tupled = "{ let (k, _) = p\n Map.updateOrInsert(k, 1, n -> n + 1, acc) }";
        String plain = "Map.updateOrInsert(p, 1, n -> n + 1, acc)";
        for (Walked each : List.of(
                new Walked("List.filter(l -> String.length(l) > 1, List.map(x -> x.label, xs))",
                        plain, "String.length(xs[*].label) > 1 && label - xs[*].label == 0"),
                new Walked("List.map(x -> x.label, List.filter(x -> x.weight >= 2, xs))", plain,
                        "xs[*].weight >= 2 && label - xs[*].label == 0"),
                new Walked("List.map(x -> (x.label, x.weight),"
                        + " List.filter(x -> x.weight >= 2, xs))", tupled,
                        "xs[*].weight >= 2 && label - xs[*].label == 0"),
                new Walked("List.map(x -> Item { label = x.label, weight = 0 }, xs)", record,
                        "label - xs[*].label == 0"),
                new Walked("List.filter(x -> x.weight >= 2, xs)", record,
                        "xs[*].weight >= 2 && label - xs[*].label == 0"),
                new Walked("List.filter(x -> x.weight >= 2, List.filter(x -> x.weight < 9, xs))",
                        record,
                        "xs[*].weight < 9 && xs[*].weight >= 2 && label - xs[*].label == 0"),
                new Walked("List.map(x -> (x.label, x.weight), xs)", tupled,
                        "label - xs[*].label == 0"))) {
            Compilation compilation = measured("""
                    module example.popular

                    data Item = { label: String, weight: Int }

                    let countsOf (xs: List<Item>): Map<String, Int> =
                        List.fold((acc, p) -> %s, Map.empty, %s)

                    behavior popular : (xs: List<Item>, label: String) -> Bool

                    let popular (xs, label) =
                        match Map.get(label, countsOf(xs)) with
                            | Some n -> n >= 3
                            | None -> false
                    """.formatted(each.step(), each.walked()));
            assertTrue(report(compilation).contains("#xs [" + each.statement() + "]"),
                    () -> each + ": " + report(compilation));
            assertFalse(report(compilation).contains("stands at no position"),
                    () -> each + ": " + report(compilation));
        }
    }

    /** An element that is to be the key asked for and to meet what it was kept by besides is no
     *  element a composer writes, and is left to the run rather than refused as malformed. */
    @Test
    void anElementKeptByItsOwnValueIsLeftToTheRun() {
        Compilation compilation = measured(modelOf(STRINGS, COUNTING, 3, "")
                .replace("Map.empty, xs)", "Map.empty, List.filter(k -> k == \"z\", xs))"));
        assertTrue(report(compilation).contains("#xs [label - xs[*] == 0 && xs[*] == z]"),
                () -> report(compilation));
    }

    /** A counter that never moves is what it starts at wherever the key occurs, so the lookup
     *  finding something is the only thing a row can turn on. */
    @Test
    void aCounterThatNeverMovesDrawsNoLineOnHowOftenTheKeyOccurs() {
        Counter still = new Counter("Map.updateOrInsert(k, 4, n -> n, acc)", 4, 0);
        Compilation compilation = measured(modelOf(STRINGS, still, 3,
                examples(List.of(STRINGS.occurs(), STRINGS.empty()), still, 3)));
        assertEquals(List.of(), borderPointsOf(compilation), () -> report(compilation));
    }

    private static final Pattern ROW = Pattern.compile("^\\[(.*)\\], (.+)$");

    /** One key of a list of them, where the last one read left off: a string or a whole number. */
    private static final Pattern KEY = Pattern.compile(
            "\\G(?:^|, )(\"(?:[^\"\\\\]|\\\\.)*\"|-?\\d+)");

    /** The rows the block offers, each read back from how it is written; a row this cannot read
     *  back to its end fails, since a part left unread is one nothing checks. */
    private static List<Row> offeredRows(Compilation compilation) {
        List<Row> out = new ArrayList<>();
        for (String each : Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("example.popular"))
                .rowsByBehavior().getOrDefault("popular", List.of()).stream()
                .map(row -> String.join(", ",
                        row.inputs().stream().map(FixtureTemplate::text).toList()))
                .toList()) {
            Matcher matched = ROW.matcher(each);
            if (!matched.matches()) {
                fail("an offered row is one this reads back: " + each);
            }
            out.add(new Row(keysIn(matched.group(1)), matched.group(2)));
        }
        return out;
    }

    private static List<String> keysIn(String list) {
        List<String> keys = new ArrayList<>();
        Matcher key = KEY.matcher(list);
        int read = 0;
        while (key.find()) {
            keys.add(key.group(1));
            read = key.end();
        }
        if (read != list.length()) {
            fail("the keys of an offered row are read to the end: " + list + " (read to " + read
                    + ")");
        }
        return keys;
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

    /** The quantity each border drawn is on, as the report names it. */
    private static List<String> borderPointsOf(Compilation compilation) {
        List<String> out = new ArrayList<>();
        borders(JSON.readTree(json(compilation)), out);
        return out;
    }

    private static void borders(JsonNode node, List<String> out) {
        if (node.isObject() && node.has("items") && node.has("axis")) {
            out.add(node.path("axis").asString() + " " + node.path("value").asString());
        }
        node.forEach(child -> borders(child, out));
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
                .map(each -> each.diagnostic().code().toString()).toList(),
                () -> "the source compiles: " + source);
        return compilation;
    }
}
