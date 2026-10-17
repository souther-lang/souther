package souther.compiler.partition;

import org.junit.jupiter.api.Test;

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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.BinaryOperator;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A map a fold builds by filing what each element holds under its key, keeping the lesser or the
 * greater of that and what was filed before, holds under a key the least or the greatest of what
 * the elements of that key hold — so a statement about one of its values is a statement about
 * that end of the key's values, and a row is composed on each side of it.
 *
 * <p>Not a statement about what any one element holds. Of two elements of one key holding four and
 * ten, the least is four, and an element holding at least seven says nothing of whether the least
 * is: a line read off the elements' own values would put a row at the wrong side of it.
 */
class AFoldThatKeepsOneEndOfWhatEachKeyFilesAnswersThatEndOfItsValuesTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String LEAST =
            "Map.updateOrInsert(t.account, t.days, seen -> Int.min(seen, t.days), acc)";

    private static final String GREATEST =
            "Map.updateOrInsert(t.account, t.days, seen -> Int.max(seen, t.days), acc)";

    /** One touch of an account. */
    private record Touch(String account, int days) {

        String written() {
            return "Touch { account = \"" + account + "\", days = " + days + " }";
        }
    }

    /** One row offered for {@code stale}: the touches and the threshold. */
    private record Row(List<Touch> touches, int staleAfter) {

        /** What the fold files under each account, keeping {@code end} of two values. */
        Map<String, Integer> filed(BinaryOperator<Integer> end) {
            Map<String, Integer> out = new LinkedHashMap<>();
            for (Touch each : touches) {
                out.merge(each.account(), each.days(), end);
            }
            return out;
        }

        /** The entries the filter keeps. */
        Map<String, Integer> kept(BinaryOperator<Integer> end) {
            Map<String, Integer> out = new LinkedHashMap<>();
            filed(end).forEach((account, days) -> {
                if (days >= staleAfter) {
                    out.put(account, days);
                }
            });
            return out;
        }

        /** The row as the language writes its inputs. */
        String written() {
            return touches.stream().map(Touch::written).toList() + ", " + staleAfter;
        }
    }

    private static String modelOf(String step, String more) {
        return """
                module example.stale

                data Touch = { account: String, days: Int }

                let sinceOf (touches: List<Touch>): Map<String, Int> =
                    List.fold((acc, t) -> %s, Map.empty, touches)

                behavior stale : (touches: List<Touch>, staleAfter: Int) -> Map<String, Int>

                let stale (touches, staleAfter) =
                    Map.filterEntries((_, days) -> days >= staleAfter, sinceOf(touches))
                %s""".formatted(step, more);
    }

    @Test
    void aLineOnTheLeastOfAKeysValuesIsOwedOfferedAndThenMet() {
        String examples = """

                example stale
                    | "none" : ([], 2) -> []
                """;
        Compilation before = measured(modelOf(LEAST, examples));
        assertEquals(List.of("ON", "OFF", "IN", "OUT"), unmetOf(before),
                () -> "every point of the line is owed: " + report(before));
        assertTrue(json(before).contains("least(touches[*].days by account)"),
                () -> "the line is on the least of a key's values: " + report(before));

        List<Row> offered = offeredRows(before);
        assertFalse(offered.isEmpty(), () -> "rows are offered: " + report(before));
        StringBuilder written = new StringBuilder(examples);
        int named = 0;
        for (Row row : offered) {
            written.append("    | \"offered ").append(named++).append("\" : (")
                    .append(row.written()).append(") -> ")
                    .append(entries(row.kept(Math::min))).append("\n");
        }
        Compilation after = measured(modelOf(LEAST, written.toString()));
        assertEquals(List.of(), unmetOf(after),
                () -> "the rows that were offered meet the line: " + report(after));
    }

    /**
     * Two elements of one key holding four and ten, against ten: the least of them is six short of
     * the line, though one of them stands on it. So the row is no row at the line, and is one well
     * short of it.
     */
    @Test
    void theLeastOfAKeyAndNotAValueOfItIsWhatTheLineIsOn() {
        Compilation compilation = measured(modelOf(LEAST, """

                example stale
                    | "four and ten" : ([%s, %s], 10) -> []
                """.formatted(new Touch("a", 4).written(), new Touch("a", 10).written())));
        List<String> unmet = unmetOf(compilation);
        assertTrue(unmet.contains("ON"), () -> "the least is not on the line: " + unmet);
        assertFalse(unmet.contains("OUT"), () -> "it is well short of it: " + unmet);
    }

    /** And the same two read for the greatest: ten, which is on the line. */
    @Test
    void theGreatestOfAKeyIsWhatTheLineIsOnForAFoldKeepingTheGreater() {
        Compilation compilation = measured(modelOf(GREATEST, """

                example stale
                    | "four and ten" : ([%s, %s], 10) -> [("a", 10)]
                """.formatted(new Touch("a", 4).written(), new Touch("a", 10).written())));
        assertTrue(json(compilation).contains("greatest(touches[*].days by account)"),
                () -> report(compilation));
        List<String> unmet = unmetOf(compilation);
        assertFalse(unmet.contains("ON"), () -> "the greatest is on the line: " + unmet);
        assertTrue(unmet.contains("OUT"), () -> "and nothing is well short of it: " + unmet);
    }

    /** Elements of another key are no part of the end of this one's values. */
    @Test
    void anotherKeysValuesAreNotTakenIntoTheEnd() {
        Compilation compilation = measured(modelOf(LEAST, """

                example stale
                    | "apart" : ([%s, %s], 10) -> [("a", 10)]
                """.formatted(new Touch("a", 10).written(), new Touch("b", 4).written())));
        List<String> unmet = unmetOf(compilation);
        assertFalse(unmet.contains("ON"), () -> "a's least is ten, on the line: " + unmet);
        assertFalse(unmet.contains("OUT"), () -> "b's least is four, well short: " + unmet);
    }

    /** Which order the elements of a key come in is no part of which end of them is kept. */
    @Test
    void theOrderOfAKeysElementsDoesNotMoveTheEnd() {
        for (List<Touch> touches : List.of(
                List.of(new Touch("a", 4), new Touch("a", 10)),
                List.of(new Touch("a", 10), new Touch("a", 4)))) {
            Compilation compilation = measured(modelOf(LEAST, """

                    example stale
                        | "two" : (%s, 4) -> [("a", 4)]
                    """.formatted(touches.stream().map(Touch::written).toList())));
            assertFalse(unmetOf(compilation).contains("ON"),
                    () -> "the least is four whichever comes first: " + touches);
        }
    }

    /** An empty list files nothing, so no entry stands at any point of the line. */
    @Test
    void anEmptyListIsNoEntryForTheLineToHoldAt() {
        Compilation compilation = measured(modelOf(LEAST, """

                example stale
                    | "none" : ([], 2) -> []
                """));
        bordersOf(compilation).forEach(border -> border.path("items").forEach(item ->
                assertFalse(item.path("hit").asBoolean(),
                        () -> "no point of the line is where nothing is filed: " + item)));
    }

    /** The end kept, written with its two values the other way round, or as a lookup and a
     *  filing, is the same end. */
    @Test
    void theSameEndWrittenAnotherWayIsTheSameLine() {
        List<String> plain = axisOf(measured(modelOf(LEAST, "")));
        for (String step : List.of(
                "Map.updateOrInsert(t.account, t.days, seen -> Int.min(t.days, seen), acc)",
                """
                match Map.get(t.account, acc) with
                        | None -> Map.insert(t.account, t.days, acc)
                        | Some seen -> Map.insert(t.account, Int.min(seen, t.days), acc)""")) {
            Compilation compilation = measured(modelOf(step, ""));
            assertEquals(plain, axisOf(compilation), () -> step + ": " + report(compilation));
        }
    }

    /**
     * The model the line was first missed in, as it was written: the map kept to its keys and
     * handed back inside a record. The comparison is read, and its line is on the least of a key's
     * values against the threshold.
     */
    @Test
    void theStaleAccountsModelReadsItsComparison() {
        Compilation compilation = measured("""
                module example.stale

                data Touch = { account: String, days: Int }

                data Report = { stale: List<String> }

                behavior staleAccounts : (touches: List<Touch>, staleAfter: Int) -> Report

                let staleAccounts (touches, staleAfter) = {
                    let since: Map<String, Int> =
                        List.fold((acc, t) -> Map.updateOrInsert(t.account, t.days, seen -> Int.min(seen, t.days), acc),
                                  Map.empty, touches)
                    Report { stale = Map.keys(Map.filterEntries((k, days) -> days >= staleAfter, since)) }
                }
                """);
        assertFalse(report(compilation).contains("not read"), () -> report(compilation));
        assertEquals(1, bordersOf(compilation).size(), () -> report(compilation));
        assertTrue(json(compilation).contains("least(touches[*].days by account)"),
                () -> report(compilation));
    }

    /** The line is written in a document the schema shipped beside this accepts. */
    @Test
    void theDocumentNamingTheEndIsOneTheSchemaAccepts() {
        for (String step : List.of(LEAST, GREATEST)) {
            DocumentShape.assertShapedLikeTheSchema(JSON.readTree(json(measured(
                    modelOf(step, "")))));
        }
    }

    /** What a fold files that keeps no end of one value of each element says nothing of it. */
    @Test
    void aFoldThatKeepsNoEndOfOneValueIsNotReadAsOne() {
        List<String> steps = List.of(
                // the first element files a value the rest are not compared on
                "Map.updateOrInsert(t.account, t.days, seen -> Int.min(seen, t.days + 1), acc)",
                // the rest are compared on another field than the first files
                "Map.updateOrInsert(t.account, t.days, seen -> Int.min(seen, String.length(t.account)), acc)",
                // what the first files turns on what came before
                "Map.updateOrInsert(t.account, Map.size(acc), seen -> Int.min(seen, Map.size(acc)), acc)",
                // under a key that turns on what came before
                "Map.updateOrInsert(String.fromInt(Map.size(acc)), t.days, seen -> Int.min(seen, t.days), acc)",
                // each element replaces what was there
                "Map.insert(t.account, t.days, acc)",
                // another key filed beside the end kept
                "Map.insert(\"other\", 9, " + LEAST + ")");
        for (String step : steps) {
            Compilation compilation = measured(modelOf(step, ""));
            assertFalse(json(compilation).contains("least("),
                    () -> "nothing is said of the least of a key's values for " + step + ": "
                            + report(compilation));
        }
    }

    private static String entries(Map<String, Integer> kept) {
        List<String> each = new ArrayList<>();
        kept.forEach((key, value) -> each.add("(\"" + key + "\", " + value + ")"));
        return each.toString();
    }

    /** The points of the lines drawn that no row is at, by name: {@code ON}, {@code OFF},
     *  {@code IN} and {@code OUT}. */
    private static List<String> unmetOf(Compilation compilation) {
        List<String> out = new ArrayList<>();
        unmet(JSON.readTree(json(compilation)), out);
        return out;
    }

    private static final Pattern POINT = Pattern.compile("^(ON|OFF|IN|OUT) point of ");

    private static void unmet(JsonNode node, List<String> out) {
        if (node.isObject() && node.has("findings")) {
            node.path("findings").forEach(finding -> {
                Matcher point = POINT.matcher(finding.path("subject").asString());
                if (point.find()) {
                    out.add(point.group(1));
                }
            });
        }
        node.forEach(child -> unmet(child, out));
    }

    /** The rows the block offers, read back from how they are written. */
    private static List<Row> offeredRows(Compilation compilation) {
        List<Row> out = new ArrayList<>();
        Pattern row = Pattern.compile("^\\[(.*)\\], (-?\\d+)$");
        Pattern touch = Pattern.compile(
                "Touch \\{ account = \"((?:[^\"\\\\]|\\\\.)*)\", days = (-?\\d+) \\}");
        for (String each : offeredInputs(compilation)) {
            Matcher matched = row.matcher(each);
            if (!matched.matches()) {
                continue;
            }
            List<Touch> touches = new ArrayList<>();
            Matcher one = touch.matcher(matched.group(1));
            while (one.find()) {
                touches.add(new Touch(one.group(1), Integer.parseInt(one.group(2))));
            }
            out.add(new Row(touches, Integer.parseInt(matched.group(2))));
        }
        return out;
    }

    private static List<String> offeredInputs(Compilation compilation) {
        return Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("example.stale"))
                .rowsByBehavior().getOrDefault("stale", List.of()).stream()
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

    /** The source measured, which is a source that compiles. */
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
