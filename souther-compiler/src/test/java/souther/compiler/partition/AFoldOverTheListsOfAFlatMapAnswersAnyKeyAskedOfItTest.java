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
 * A map a fold builds by filing a counter under each element of the lists of an outer list put end
 * to end answers a lookup of any key with how often that key occurs across all of those lists:
 * nothing where it occurs in none of them, and what the counter comes to where it does. The
 * lookup finding something and the counter it finds are of one count, so the lines they draw fall
 * on the same number, and rows are composed on each side of them.
 */
class AFoldOverTheListsOfAFlatMapAnswersAnyKeyAskedOfItTest {

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

    /** One row offered for {@code popular}: the lists of the outer list and the key asked for,
     *  each as the language writes it. */
    private record Row(String lists, String label) {

        private static final Pattern KEY = Pattern.compile("\"(?:[^\"\\\\]|\\\\.)*\"|-?\\d+");

        /** How often the key asked for occurs across all of the lists. */
        long occurrences() {
            long seen = 0;
            Matcher key = KEY.matcher(lists);
            while (key.find()) {
                if (key.group().equals(label)) {
                    seen++;
                }
            }
            return seen;
        }

        /** How many lists of the outer list hold the key. */
        long listsHoldingIt() {
            return Pattern.compile("\\[[^\\[\\]]*\\]").matcher(lists).results()
                    .filter(each -> {
                        Matcher key = KEY.matcher(each.group());
                        while (key.find()) {
                            if (key.group().equals(label)) {
                                return true;
                            }
                        }
                        return false;
                    }).count();
        }

        /** What {@code popular} answers: the lookup finds nothing where the key never occurs. */
        boolean popular(Counter counter, int atLeast) {
            long seen = occurrences();
            return seen > 0 && counter.after(seen) >= atLeast;
        }

        String written() {
            return lists + ", " + label;
        }
    }

    /** A key type, with the rows the examples that name the behavior are written from: one where
     *  the key occurs in two lists and one where nothing does. */
    private record Keys(String type, Row occurs, Row empty) { }

    private static final Keys STRINGS = new Keys("String",
            new Row("[[\"a\", \"a\"], [\"a\"]]", "\"a\""), new Row("[]", "\"a\""));

    private static final Keys INTS = new Keys("Int",
            new Row("[[7, 7], [7]]", "7"), new Row("[]", "7"));

    private static String modelOf(Keys keys, Counter counter, int atLeast, String more) {
        return """
                module example.popular

                let countsOf (xss: List<List<%1$s>>): Map<%1$s, Int> =
                    List.fold((acc, k) -> %2$s, Map.empty, List.flatMap(xs -> xs, xss))

                behavior popular : (xss: List<List<%1$s>>, label: %1$s) -> Bool

                let popular (xss, label) =
                    match Map.get(label, countsOf(xss)) with
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
        List<Boolean> byOccurrences = java.util.stream.IntStream.rangeClosed(1, 8).boxed()
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
    void aLineOnHowOftenTheKeyOccursAcrossTheListsIsOwedOfferedAndThenMet() {
        assertTheLineIsOfferedAndMet(STRINGS, COUNTING, 3);
    }

    @Test
    void theKeyIsCountedWhateverItsTypeIs() {
        assertTheLineIsOfferedAndMet(INTS, COUNTING, 3);
    }

    /** The count is across the lists: a row that put every occurrence in one list would not tell
     *  it from a count inside one. */
    @Test
    void theOccurrencesAreSpreadOverMoreThanOneList() {
        List<Row> rows = offeredRows(measured(modelOf(STRINGS, COUNTING, 3, "")));
        assertTrue(rows.stream().anyMatch(row -> row.occurrences() == 3
                && row.listsHoldingIt() > 1), () -> "a count of three across lists: " + rows);
    }

    @Test
    void theLineIsOnHowOftenTheKeyOccursAgainstTheThreshold() {
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

    /** A key that occurs in no list of an outer list that holds some is a lookup finding nothing,
     *  and the lookup finding nothing and finding something are drawn on one number. */
    @Test
    void theLookupFindingNothingAndFindingSomethingAreOneCount() {
        String report = report(measured(modelOf(STRINGS, COUNTING, 3, "")));
        assertTrue(report.contains("occurrences(xss[*][*] equal to label)"), () -> report);
        assertFalse(report.contains("stands at no position"), () -> report);
        assertFalse(report.contains("stands at no one value"), () -> report);
    }

    /** A key among none of the lists of an outer list that holds some, or whose lists are empty,
     *  is a lookup finding nothing, and meets the line as a row of its own. */
    @Test
    void aKeyThatOccursInNoListOfAnOuterListThatHasSomeFindsNothing() {
        List<Row> absent = List.of(
                new Row("[[\"a\", \"a\"], [\"b\"]]", "\"c\""),
                new Row("[[], []]", "\"a\""));
        for (Row row : absent) {
            assertEquals(0, row.occurrences(), row::toString);
        }
        List<Row> rows = new ArrayList<>(List.of(STRINGS.occurs()));
        rows.addAll(absent);
        Compilation compilation = measured(modelOf(STRINGS, COUNTING, 3,
                examples(rows, COUNTING, 3)));
        assertFalse(report(compilation).contains("`case None`"),
                () -> "the rows that find nothing take that arm: " + report(compilation));
    }

    private static final Pattern ROW = Pattern.compile("^(\\[.*\\]), (\"(?:[^\"\\\\]|\\\\.)*\"|-?\\d+)$");

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
            out.add(new Row(matched.group(1), matched.group(2)));
        }
        return out;
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
