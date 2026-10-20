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
import java.util.Map;
import java.util.TreeMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * A lookup in a map a fold built by filing under the key of each element, under a key read off
 * that same map's keys, finds the entry filed under it: what it finds is the value of an entry,
 * read as {@code Map.filterEntries} reads it, and the arm finding nothing is taken by no run.
 *
 * <p>So walking the keys and looking each one up draws the line walking the entries does, and the
 * rows offered for it are the same rows.
 */
class ALookupUnderOneOfAMapsOwnKeysFindsTheEntryUnderItTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String COUNTED = "Map.updateOrInsert(t.account, 1, n -> n + 1, acc)";

    private static final String LEAST =
            "Map.updateOrInsert(t.account, t.days, seen -> Int.min(seen, t.days), acc)";

    /** The entries kept, then their keys. */
    private static final String THROUGH_THE_ENTRIES =
            "Map.keys(Map.filterEntries((_, d) -> d >= staleAfter, since))";

    /** Each key looked up where it is walked. */
    private static final String LOOKED_UP_INLINE = """
            List.filter(a -> match Map.get(a, since) with
                                | Some d -> d >= staleAfter
                                | None -> false, Map.keys(since))""";

    /** Each key looked up by a helper that says the key is the map's own, over the keys sorted. */
    private static final String LOOKED_UP_BY_A_HELPER =
            "List.filter(a -> lookup(since, a) >= staleAfter, List.sort(Map.keys(since)))";

    private static String modelOf(String step, String kept, String examples) {
        return """
                module example.stale

                data Touch = { account: String, days: Int }

                let sinceOf (touches: List<Touch>): Map<String, Int> =
                    List.fold((acc, t) -> %s, Map.empty, touches)

                let lookup (m: Map<String, Int>, account: String): Int =
                    match Map.get(account, m) with
                        | Some figure -> figure
                        | None -> unreachable "the account was read from the keys of this map"

                behavior stale : (touches: List<Touch>, staleAfter: Int) -> List<String>

                let stale (touches, staleAfter) = {
                    let since = sinceOf(touches)
                    %s
                }
                %s""".formatted(step, kept, examples);
    }

    @Test
    void walkingTheKeysDrawsTheLineWalkingTheEntriesDraws() {
        for (String step : List.of(COUNTED, LEAST)) {
            Compilation entries = measured(modelOf(step, THROUGH_THE_ENTRIES, ""));
            List<String> line = axisOf(entries);
            assertEquals(1, line.size(), () -> step + ": " + report(entries));
            for (String kept : List.of(LOOKED_UP_INLINE, LOOKED_UP_BY_A_HELPER)) {
                Compilation keys = measured(modelOf(step, kept, ""));
                assertEquals(notReadOf(entries), notReadOf(keys),
                        () -> step + "\n" + kept + "\n" + report(keys));
                assertEquals(line, axisOf(keys), () -> step + "\n" + kept + "\n" + report(keys));
                assertEquals(offeredInputs(entries), offeredInputs(keys),
                        () -> step + "\n" + kept);
            }
        }
    }

    /** The rows offered for the keys looked up by the helper, written with what the behavior
     *  answers on each, are at every point of the line. */
    @Test
    void theRowsOfferedForTheKeysLookedUpMeetTheLine() {
        String none = """

                example stale
                    | "none" : ([], 2) -> []
                """;
        Compilation before = measured(modelOf(LEAST, LOOKED_UP_BY_A_HELPER, none));
        assertEquals(List.of("ON", "OFF", "IN", "OUT"), unmetOf(before), () -> report(before));
        StringBuilder written = new StringBuilder(none);
        int named = 0;
        for (String row : offeredInputs(before)) {
            written.append("    | \"offered ").append(named++).append("\" : (").append(row)
                    .append(") -> ").append(staleOf(row)).append("\n");
        }
        assertTrue(named > 0, () -> report(before));
        Compilation after = measured(modelOf(LEAST, LOOKED_UP_BY_A_HELPER, written.toString()));
        assertEquals(List.of(), unmetOf(after), () -> report(after));
    }

    /** A key of one map looked up in another finds whatever that one holds under it, which is
     *  no entry of the first: the comparison is not read as one. */
    @Test
    void aKeyOfOneMapLookedUpInAnotherIsNotItsEntry() {
        Compilation compilation = measured("""
                module example.stale

                data Touch = { account: String, days: Int }

                let sinceOf (touches: List<Touch>): Map<String, Int> =
                    List.fold((acc, t) -> %s, Map.empty, touches)

                behavior stale : (touches: List<Touch>, others: List<Touch>, staleAfter: Int)
                    -> List<String>

                let stale (touches, others, staleAfter) = {
                    let since = sinceOf(touches)
                    let elsewhere = sinceOf(others)
                    List.filter(a -> match Map.get(a, elsewhere) with
                                        | Some d -> d >= staleAfter
                                        | None -> false, Map.keys(since))
                }
                """.formatted(COUNTED));
        assertTrue(report(compilation).contains("not read"), () -> report(compilation));
    }

    private static final Pattern NOT_READ =
            Pattern.compile("not read: comparison@\\d+:\\d+ — (.*)$", Pattern.MULTILINE);

    /** What the report says was not read, and why, without where the comparison was written. */
    private static List<String> notReadOf(Compilation compilation) {
        List<String> out = new ArrayList<>();
        Matcher each = NOT_READ.matcher(report(compilation));
        while (each.find()) {
            out.add(each.group(1));
        }
        return out;
    }

    private static final Pattern ROW = Pattern.compile("^\\[(.*)\\], (-?\\d+)$");

    private static final Pattern TOUCH = Pattern.compile(
            "\\G(?:^|, )Touch \\{ account = \"((?:[^\"\\\\]|\\\\.)*)\", days = (-?\\d+) \\}");

    /** What {@code stale} answers on the row written {@code row}: the accounts whose least days
     *  are at least the threshold, in order. */
    private static String staleOf(String row) {
        Matcher matched = ROW.matcher(row);
        if (!matched.matches()) {
            fail("an offered row is one this reads back: " + row);
        }
        Map<String, Integer> least = new TreeMap<>();
        Matcher one = TOUCH.matcher(matched.group(1));
        int read = 0;
        while (one.find()) {
            least.merge(one.group(1), Integer.parseInt(one.group(2)), Math::min);
            read = one.end();
        }
        if (read != matched.group(1).length()) {
            fail("the touches of an offered row are read to the end: " + row);
        }
        int staleAfter = Integer.parseInt(matched.group(2));
        List<String> stale = new ArrayList<>();
        least.forEach((account, days) -> {
            if (days >= staleAfter) {
                stale.add("\"" + account + "\"");
            }
        });
        return stale.toString();
    }

    private static List<String> offeredInputs(Compilation compilation) {
        return Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("example.stale"))
                .rowsByBehavior().getOrDefault("stale", List.of()).stream()
                .map(row -> String.join(", ",
                        row.inputs().stream().map(FixtureTemplate::text).toList()))
                .toList();
    }

    /** The points of the lines drawn that no row is at, by name. */
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

    /** The quantity each border is on, as the report names it. */
    private static List<String> axisOf(Compilation compilation) {
        List<String> out = new ArrayList<>();
        collect(JSON.readTree(json(compilation)), out);
        return out;
    }

    private static void collect(JsonNode node, List<String> out) {
        if (node.isObject() && node.has("items") && node.has("axis")) {
            out.add(node.path("axis").asString() + " " + node.path("value").asString());
        }
        node.forEach(child -> collect(child, out));
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
