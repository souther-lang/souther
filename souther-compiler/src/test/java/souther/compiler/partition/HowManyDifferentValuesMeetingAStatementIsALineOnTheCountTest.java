package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.meaning.Quantity;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many different values the elements meeting a statement hold at one place of each is a
 * number a rule can draw a line on ({@link Quantity.HowManyDifferentMeet}), and a row stands on
 * that line where that many values are held by elements meeting it.
 *
 * <p>Written over a filter, the statement is asked of each element: a value is counted where some
 * element holding it meets it. Written over the entries a fold filed under the value, it is asked
 * of what the elements of each value come to. {@code 10} and {@code -10} under one currency tell
 * the two apart: one of them is above nought, and their total is not.
 *
 * <p>Every example below is run, so the answer it writes is what the language computes; which point
 * it hits is what the line reads of it. The two are the same row.
 */
class HowManyDifferentValuesMeetingAStatementIsALineOnTheCountTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String HEAD = """
            module probe

            data Forecast = { currency: String, amount: Int }

            let filed (cs: List<String>): Map<String, Int> =
                List.fold((acc, c) -> Map.updateOrInsert(c, 1, n -> n + 1, acc), Map.empty, cs)

            let totalsOf (fs: List<Forecast>): Map<String, Int> =
                List.fold((acc, f) -> Map.updateOrInsert(f.currency, f.amount,
                    n -> n + f.amount, acc), Map.empty, fs)

            behavior f : (fs: List<Forecast>) -> Int
            let f (fs) = if %s then 1 else 0
            """;

    private static final String OF_EACH_ELEMENT =
            "#different fs [fs[*].currency] where [fs[*].amount > 0]";

    private static final String OF_EACH_VALUE =
            "#different fs [fs[*].currency] where [total(fs[*].amount by currency) > 0]";

    /** However the different values of the elements a filter kept are counted, one count. */
    @Test
    void everyWayOfCountingTheValuesAFilterKeptIsOneCount() {
        for (String count : List.of(
                "Set.size(Set.fromList(List.map(.currency, List.filter(f -> f.amount > 0, fs))))",
                "List.length(List.distinct(List.map(.currency,"
                        + " List.filter(f -> f.amount > 0, fs))))",
                "Set.size(List.fold((acc, f) -> Set.insert(f.currency, acc), Set.empty,"
                        + " List.filter(f -> f.amount > 0, fs)))",
                "Map.size(filed(List.map(.currency, List.filter(f -> f.amount > 0, fs))))")) {
            JsonNode line = only(differentCounts(reportOf(HEAD.formatted(count + " == 1"))));
            assertEquals(OF_EACH_ELEMENT, line.at("/lineId/target/quantity/counted").asString(),
                    count);
        }
    }

    /** And how many entries of a fold's map a statement keeps is a count of the values whose
     *  total meets it. */
    @Test
    void theEntriesAStatementKeepsOfAFoldsMapAreTheValuesWhoseTotalMeetsIt() {
        JsonNode line = only(differentCounts(reportOf(HEAD.formatted(
                "Map.size(Map.filterEntries((_, n) -> n > 0, totalsOf(fs))) == 1"))));
        assertEquals(OF_EACH_VALUE, line.at("/lineId/target/quantity/counted").asString());
    }

    /**
     * Asked of each element, {@code 10} under a currency keeps the currency whatever else is under
     * it, and two elements of one currency are one value.
     */
    @Test
    void aValueIsCountedWhereSomeElementHoldingItMeetsTheStatement() {
        JsonNode line = only(differentCounts(reportOf(HEAD.formatted(
                "Set.size(Set.fromList(List.map(.currency, List.filter(f -> f.amount > 0, fs))))"
                        + " == 1") + """
                example f
                    | "one of two above nought" : ([Forecast { currency = "USD", amount = 10 },
                        Forecast { currency = "USD", amount = -10 }]) -> 1
                """)));
        assertTrue(pointAt(line, "on").path("hit").asBoolean(), line::toString);

        JsonNode twice = only(differentCounts(reportOf(HEAD.formatted(
                "Set.size(Set.fromList(List.map(.currency, List.filter(f -> f.amount > 0, fs))))"
                        + " == 1") + """
                example f
                    | "two of one currency" : ([Forecast { currency = "USD", amount = 10 },
                        Forecast { currency = "USD", amount = 20 }]) -> 1
                """)));
        assertTrue(pointAt(twice, "on").path("hit").asBoolean(), twice::toString);

        JsonNode two = only(differentCounts(reportOf(HEAD.formatted(
                "Set.size(Set.fromList(List.map(.currency, List.filter(f -> f.amount > 0, fs))))"
                        + " == 1") + """
                example f
                    | "two currencies" : ([Forecast { currency = "USD", amount = 10 },
                        Forecast { currency = "EUR", amount = 20 }]) -> 0
                """)));
        assertFalse(pointAt(two, "on").path("hit").asBoolean(), two::toString);
        assertTrue(pointsAt(two, "off").stream().anyMatch(off -> off.path("hit").asBoolean()
                && "2".equals(off.path("against").asString())), two::toString);
    }

    /**
     * Asked of what the elements of each value come to, {@code 10} and {@code -10} under one
     * currency total nought and keep nothing, though one of them is above nought on its own.
     */
    @Test
    void aValueIsCountedWhereWhatItsElementsComeToMeetsTheStatement() {
        JsonNode cancelled = only(differentCounts(reportOf(HEAD.formatted(
                "Map.size(Map.filterEntries((_, n) -> n > 0, totalsOf(fs))) == 1") + """
                example f
                    | "one of two above nought" : ([Forecast { currency = "USD", amount = 10 },
                        Forecast { currency = "USD", amount = -10 }]) -> 0
                """)));
        assertFalse(pointAt(cancelled, "on").path("hit").asBoolean(), cancelled::toString);
        assertTrue(pointsAt(cancelled, "off").stream().anyMatch(off -> off.path("hit").asBoolean()
                && "0".equals(off.path("against").asString())), cancelled::toString);

        JsonNode kept = only(differentCounts(reportOf(HEAD.formatted(
                "Map.size(Map.filterEntries((_, n) -> n > 0, totalsOf(fs))) == 1") + """
                example f
                    | "below nought on its own" : ([Forecast { currency = "USD", amount = 20 },
                        Forecast { currency = "USD", amount = -10 },
                        Forecast { currency = "EUR", amount = -5 }]) -> 1
                """)));
        assertTrue(pointAt(kept, "on").path("hit").asBoolean(), kept::toString);
    }

    /** How often a value occurs is what its elements come to as well: a currency held twice is
     *  kept by a statement that it is held twice, and one held once is not. */
    @Test
    void aValueIsCountedWhereHowOftenItOccursMeetsTheStatement() {
        JsonNode line = only(differentCounts(reportOf(HEAD.formatted(
                "Map.size(Map.filterEntries((_, n) -> n >= 2, filed(List.map(.currency, fs))))"
                        + " == 1") + """
                example f
                    | "one currency twice" : ([Forecast { currency = "USD", amount = 1 },
                        Forecast { currency = "EUR", amount = 1 },
                        Forecast { currency = "USD", amount = 1 }]) -> 1
                """)));
        assertEquals("#different fs [fs[*].currency] where [multiplicity(fs[*].currency) >= 2]",
                line.at("/lineId/target/quantity/counted").asString());
        assertTrue(pointAt(line, "on").path("hit").asBoolean(), line::toString);
    }

    /**
     * Every point of a line on either count has a row composed for it, two values above one held
     * by elements of different values, and below none is no count at all. Where elements of one
     * value meet the statement more than one way — on either side of five — two of them are
     * still one value, and two values are two elements of different ones.
     */
    @Test
    void everyPointOfALineOnEitherCountHasARowComposedForIt() {
        for (String count : List.of(
                "Set.size(Set.fromList(List.map(.currency, List.filter(f -> f.amount > 0, fs))))",
                "Set.size(Set.fromList(List.map(.currency,"
                        + " List.filter(f -> f.amount > 0 && f.amount /= 5, fs))))",
                "Map.size(Map.filterEntries((_, n) -> n > 0, totalsOf(fs)))")) {
            for (String against : List.of(" >= 2", " == 1")) {
                JsonNode line = only(differentCounts(reportOf(HEAD.formatted(count + against))));
                for (JsonNode item : line.path("items")) {
                    if (item.has("notOwed")) {
                        assertEquals("no_value_can_stand_there", item.path("notOwed").asString(),
                                item::toString);
                        continue;
                    }
                    List<String> because = new ArrayList<>();
                    item.path("writableBecause").forEach(each -> because.add(each.asString()));
                    assertTrue(item.path("knownWritable").asBoolean()
                            && because.contains("a_value_was_built"),
                            () -> count + against + ": " + item);
                }
            }
        }
    }

    /**
     * A line reached only where the count is one has rows composed for it holding one value kept
     * by the statement, as a line reached under a count of the elements does.
     */
    @Test
    void aLineReachedWhereTheCountIsOneHasRowsComposedForItHoldingOneValue() {
        JsonNode report = reportOf(HEAD.formatted(
                "Set.size(Set.fromList(List.map(.currency, List.filter(f -> f.amount > 0, fs))))"
                        + " == 1 && List.length(fs) >= 3"));
        JsonNode length = null;
        for (JsonNode each : behaviorOf(report).at("/partition/boundaries")) {
            if ("f/List.length(fs)".equals(each.path("axis").asString())) {
                length = each;
            }
        }
        assertTrue(length != null, report::toString);
        for (JsonNode item : length.path("items")) {
            assertTrue(item.path("knownWritable").asBoolean(), item::toString);
        }
    }

    /**
     * A count recognised that no line can be drawn on — the different values of one container
     * against those of another — is a rule nobody read, and no row is offered for it.
     */
    @Test
    void aCountNoLineIsDrawnOnIsStillARuleNobodyRead() {
        JsonNode report = reportOf(HEAD.formatted(
                "Set.size(Set.fromList(List.map(.currency, List.filter(f -> f.amount > 0, fs))))"
                        + " == Set.size(Set.fromList(List.map(.currency, fs)))"));
        assertEquals(List.of(), differentCounts(report));
        assertTrue(behaviorOf(report).path("weakening").toString().contains("rule_unread"),
                report::toString);
    }

    /**
     * The comparison the filter's closure writes is read where it is written, as its own line on
     * the element's number, and the count beside it leaves nothing of the input unread.
     */
    @Test
    void theClosuresComparisonIsItsOwnLineAndTheCountLeavesNothingUnread() {
        JsonNode report = reportOf(HEAD.formatted(
                "Set.size(Set.fromList(List.map(.currency, List.filter(f -> f.amount > 0, fs))))"
                        + " >= 2"));
        JsonNode behavior = behaviorOf(report);
        List<String> axes = new ArrayList<>();
        behavior.at("/partition/boundaries").forEach(each -> axes.add(each.path("axis")
                .asString()));
        assertTrue(axes.contains("f/fs[*].amount"), axes::toString);
        assertFalse(behavior.path("weakening").toString().contains("rule_unread"),
                behavior.path("weakening")::toString);
        List<String> unread = new ArrayList<>();
        behavior.at("/partition/notRead").forEach(each -> unread.add(each.path("position")
                .asString() + " " + each.path("reason").asString()));
        assertEquals(List.of("fs[*].amount rule_about_a_run"), unread);
    }

    private static JsonNode reportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList());
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList(),
                "every example answers what it writes");
        return JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
    }

    private static JsonNode behaviorOf(JsonNode report) {
        for (JsonNode each : report.at("/modules/0/behaviors")) {
            if ("f".equals(each.path("name").asString())) {
                return each;
            }
        }
        throw new AssertionError("a behavior f in " + report);
    }

    private static List<JsonNode> differentCounts(JsonNode report) {
        List<JsonNode> out = new ArrayList<>();
        collect(report, out);
        return out;
    }

    private static void collect(JsonNode node, List<JsonNode> out) {
        if (node.isObject() && node.has("items")
                && "count_of_different_values".equals(node.path("kind").asString())) {
            out.add(node);
        }
        node.forEach(child -> collect(child, out));
    }

    private static JsonNode only(List<JsonNode> lines) {
        assertEquals(1, lines.size(), () -> "one line on the count: " + lines);
        return lines.getFirst();
    }

    private static JsonNode pointAt(JsonNode line, String point) {
        return pointsAt(line, point).getFirst();
    }

    private static List<JsonNode> pointsAt(JsonNode line, String point) {
        List<JsonNode> out = new ArrayList<>();
        line.path("items").forEach(each -> {
            if (point.equals(each.path("point").asString())) {
                out.add(each);
            }
        });
        if (out.isEmpty()) {
            throw new AssertionError("a " + point + " point on " + line);
        }
        return out;
    }
}
