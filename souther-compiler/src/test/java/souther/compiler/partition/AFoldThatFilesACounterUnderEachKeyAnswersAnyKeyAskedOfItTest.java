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

    /** One row offered for {@code popular}: the keys of the list and the key asked for. */
    private record Row(List<String> keys, String label) {

        /** How often the key asked for occurs. */
        long occurrences() {
            return keys.stream().filter(label::equals).count();
        }

        /** What {@code popular} answers with a counter that starts at {@code first} and adds
         *  {@code step}, against {@code atLeast}. */
        boolean popular(int first, int step, int atLeast) {
            long seen = occurrences();
            return seen > 0 && first + (seen - 1) * step >= atLeast;
        }

        String written() {
            return keys.stream().map(each -> "\"" + each + "\"").toList()
                    + ", \"" + label + "\"";
        }
    }

    private static String modelOf(String step, int atLeast, String more) {
        return """
                module example.popular

                let countsOf (xs: List<String>): Map<String, Int> =
                    List.fold((acc, k) -> %s, Map.empty, xs)

                behavior popular : (xs: List<String>, label: String) -> Bool

                let popular (xs, label) =
                    match Map.get(label, countsOf(xs)) with
                        | Some n -> n >= %d
                        | None -> false
                %s""".formatted(step, atLeast, more);
    }

    private static final String COUNTING = "Map.updateOrInsert(k, 1, n -> n + 1, acc)";

    /** The examples that name the behavior, so that rows are offered for it: one where the key
     *  occurs and one where nothing does. */
    private static String seeded(int first, int step, int atLeast) {
        return examples(List.of(new Row(List.of("a", "a", "a"), "a"), new Row(List.of(), "a")),
                first, step, atLeast);
    }

    private static String examples(List<Row> rows, int first, int step, int atLeast) {
        StringBuilder written = new StringBuilder("\nexample popular\n");
        int named = 0;
        for (Row row : rows) {
            written.append("    | \"row ").append(named++).append("\" : (").append(row.written())
                    .append(") -> ").append(row.popular(first, step, atLeast)).append("\n");
        }
        return written.toString();
    }

    @Test
    void aLineOnHowOftenTheKeyAskedForOccursIsOwedOfferedAndThenMet() {
        Compilation before = measured(modelOf(COUNTING, 3, seeded(1, 1, 3)));
        assertFalse(unmetOf(before).isEmpty(), () -> "the line is owed: " + report(before));

        List<Row> offered = offeredRows(before);
        assertFalse(offered.isEmpty(), () -> "rows are offered: " + report(before));

        List<Row> all = new ArrayList<>(List.of(
                new Row(List.of("a", "a", "a"), "a"), new Row(List.of(), "a")));
        all.addAll(offered);
        Compilation after = measured(modelOf(COUNTING, 3, examples(all, 1, 1, 3)));
        assertEquals(List.of(), unmetOf(after),
                () -> "the rows that were offered meet the line: " + report(after));
    }

    @Test
    void theLineIsOnHowOftenTheKeyAskedForOccursAgainstTheThreshold() {
        List<Row> rows = offeredRows(measured(modelOf(COUNTING, 3, "")));
        assertTrue(rows.stream().anyMatch(row -> row.occurrences() == 3),
                () -> "a row whose key occurs at the threshold: " + rows);
        assertTrue(rows.stream().anyMatch(row -> row.occurrences() == 2),
                () -> "a row whose key occurs one short of it: " + rows);
        assertTrue(rows.stream().anyMatch(row -> row.occurrences() > 3),
                () -> "a row whose key occurs past it: " + rows);
        assertTrue(rows.stream().anyMatch(row -> row.occurrences() == 0),
                () -> "a row whose key never occurs: " + rows);
    }

    @Test
    void whatTheCounterStartsAtAndAddsMovesTheLine() {
        record Fold(String step, int first, int add) { }
        for (Fold fold : List.of(
                new Fold("Map.updateOrInsert(k, 2, n -> n + 3, acc)", 2, 3),
                new Fold("Map.updateOrInsert(k, 5, n -> n - 1, acc)", 5, -1))) {
            Compilation before = measured(
                    modelOf(fold.step(), 6, seeded(fold.first(), fold.add(), 6)));
            List<Row> all = new ArrayList<>(List.of(
                    new Row(List.of("a", "a", "a"), "a"), new Row(List.of(), "a")));
            all.addAll(offeredRows(before));
            Compilation after = measured(modelOf(fold.step(), 6,
                    examples(all, fold.first(), fold.add(), 6)));
            assertEquals(List.of(), unmetOf(after),
                    () -> fold + " meets the line with the rows offered: " + report(after));
        }
    }

    /**
     * The list a fold walks may be a position's elements kept by a statement, or a tuple a map
     * built of each: the key asked for occurs among the elements meeting what they were kept by,
     * and the key of an element is the place it was given. The line is drawn on that count, and
     * the lookup finding nothing is told apart from it as before.
     */
    @Test
    void theElementsAFoldWalksAreThosePutToItInsteadOfThePositionsOwn() {
        record Walked(String walked, String step, String statement) { }
        String record = "Map.updateOrInsert(p.label, 1, n -> n + 1, acc)";
        String tupled = "{ let (k, _) = p\n Map.updateOrInsert(k, 1, n -> n + 1, acc) }";
        for (Walked each : List.of(
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
        Compilation compilation = measured(modelOf(COUNTING, 3, "").replace("Map.empty, xs)",
                "Map.empty, List.filter(k -> k == \"z\", xs))"));
        assertTrue(report(compilation).contains("#xs [label - xs[*] == 0 && xs[*] == z]"),
                () -> report(compilation));
    }

    /** A counter that never moves is what it starts at wherever the key occurs, so the lookup
     *  finding something is the only thing a row can turn on. */
    @Test
    void aCounterThatNeverMovesDrawsNoLineOnHowOftenTheKeyOccurs() {
        Compilation compilation = measured(modelOf("Map.updateOrInsert(k, 4, n -> n, acc)", 3,
                seeded(4, 0, 3)));
        assertEquals(List.of(), borderPointsOf(compilation), () -> report(compilation));
    }

    private static final Pattern ROW = Pattern.compile("^\\[(.*)\\], \"((?:[^\"\\\\]|\\\\.)*)\"$");

    private static final Pattern KEY = Pattern.compile(
            "\\G(?:^|, )\"((?:[^\"\\\\]|\\\\.)*)\"");

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
