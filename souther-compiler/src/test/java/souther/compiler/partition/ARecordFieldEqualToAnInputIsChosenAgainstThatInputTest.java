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

/**
 * An element of a container that is a record is chosen by values for each of its fields, and a
 * field a statement compares with another input turns over at that input's value, so the field's
 * values are read with the input where it stands. Rows are composed on each side of the line
 * however the field reaches the statement: counted directly, as the key a fold files a counter
 * under, or as a component of a tuple a walk made of each element.
 */
class ARecordFieldEqualToAnInputIsChosenAgainstThatInputTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String ITEM = "data Item = { label: String, weight: Int }\n";

    /** A way the field reaches the statement: the behavior's body, over {@code xs} and
     *  {@code label}. */
    private record Reaching(String name, String declarations, String body) { }

    private static final List<Reaching> WAYS = List.of(
            new Reaching("counted directly", "",
                    "List.length(List.filter(x -> x.label == label, xs)) >= 3"),
            new Reaching("the key a fold files under", """

                    let countsOf (xs: List<Item>): Map<String, Int> =
                        List.fold((acc, p) -> Map.updateOrInsert(p.label, 1, n -> n + 1, acc),
                            Map.empty, xs)
                    """, lookup()),
            new Reaching("a component of a tuple", """

                    let countsOf (xs: List<Item>): Map<String, Int> =
                        List.fold((acc, p) -> { let (k, _) = p
                            Map.updateOrInsert(k, 1, n -> n + 1, acc) },
                            Map.empty, List.map(x -> (x.label, x.weight), xs))
                    """, lookup()));

    private static String lookup() {
        return """
                match Map.get(label, countsOf(xs)) with
                    | Some n -> n >= 3
                    | None -> false""";
    }

    private static String modelOf(Reaching way, String examples) {
        return "module example.popular\n\n" + ITEM + way.declarations() + """

                behavior popular : (xs: List<Item>, label: String) -> Bool

                let popular (xs, label) =
                    %s
                %s""".formatted(way.body().replace("\n", "\n    "), examples);
    }

    /** One row offered for {@code popular}: the items of the list and the label beside it, each as
     *  the language writes it. */
    private record Row(String items, String label) {

        private static final Pattern ITEM_LABEL =
                Pattern.compile("label = (\"(?:[^\"\\\\]|\\\\.)*\")");

        /** How many items carry the label. */
        long meeting() {
            Matcher item = ITEM_LABEL.matcher(items);
            long meeting = 0;
            while (item.find()) {
                if (item.group(1).equals(label)) {
                    meeting++;
                }
            }
            return meeting;
        }

        String written() {
            return items + ", " + label;
        }
    }

    @Test
    void rowsAreComposedOnEachSideOfTheLineWhicheverWayTheFieldReachesTheStatement() {
        for (Reaching way : WAYS) {
            Compilation owing = measured(modelOf(way, ""));
            // Every way a decision goes is a row this composes toward, and none is left to the
            // run for being an item held to a value outside it.
            assertFalse(report(owing).contains("two values being one"),
                    () -> way.name() + ": " + report(owing));
            List<Row> offered = offeredRows(owing);
            List<Long> meeting = offered.stream().map(Row::meeting).toList();
            assertTrue(meeting.contains(3L), () -> way.name() + " at the line: " + meeting);
            assertTrue(meeting.contains(2L), () -> way.name() + " one short: " + meeting);
            assertTrue(meeting.stream().anyMatch(each -> each > 3),
                    () -> way.name() + " past it: " + meeting);
            assertTrue(meeting.stream().anyMatch(each -> each < 2),
                    () -> way.name() + " short of it: " + meeting);
        }
    }

    /** The rows offered, written as examples, meet every line, and every way a decision goes. */
    @Test
    void theRowsOfferedMeetTheLineAndTakeEveryRuleWhicheverWayTheFieldReachesTheStatement() {
        for (Reaching way : WAYS) {
            List<Row> offered = new ArrayList<>(offeredRows(measured(modelOf(way, ""))));
            // And an item the label does not match, which no row at a line needs one of.
            offered.add(new Row("[Item { label = \"b\", weight = 0 }]", "\"a\""));
            Compilation after = measured(modelOf(way, examples(offered)));
            assertEquals(List.of(), unmetOf(after), () -> way.name() + ": " + report(after));
            assertFalse(report(after).contains("no row takes a decision rule"),
                    () -> way.name() + ": " + report(after));
            assertFalse(report(after).contains("two values being one"),
                    () -> way.name() + ": " + report(after));
        }
    }

    private static String examples(List<Row> rows) {
        StringBuilder written = new StringBuilder("\nexample popular\n");
        int named = 0;
        for (Row row : rows) {
            written.append("    | \"row ").append(named++).append("\" : (").append(row.written())
                    .append(") -> ").append(row.meeting() >= 3).append("\n");
        }
        return written.toString();
    }

    private static final Pattern ROW = Pattern.compile(
            "^(\\[.*\\]), (\"(?:[^\"\\\\]|\\\\.)*\")$");

    private static List<Row> offeredRows(Compilation compilation) {
        List<Row> out = new ArrayList<>();
        for (String each : Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("example.popular"))
                .rowsByBehavior().getOrDefault("popular", List.of()).stream()
                .map(row -> String.join(", ",
                        row.inputs().stream().map(FixtureTemplate::text).toList()))
                .toList()) {
            Matcher matched = ROW.matcher(each);
            assertTrue(matched.matches(), () -> "an offered row is one this reads back: " + each);
            out.add(new Row(matched.group(1), matched.group(2)));
        }
        return out;
    }

    /** The points of the lines drawn that no row is at. */
    private static List<String> unmetOf(Compilation compilation) {
        List<String> out = new ArrayList<>();
        unmet(JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE))), out);
        return out;
    }

    private static void unmet(JsonNode node, List<String> out) {
        if (node.isObject() && "unmet".equals(node.path("disposition").asString())) {
            out.add(node.path("relation").asString());
        }
        node.forEach(child -> unmet(child, out));
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

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
