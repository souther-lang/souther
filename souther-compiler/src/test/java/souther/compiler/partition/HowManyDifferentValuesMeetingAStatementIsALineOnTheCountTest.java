package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
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

    private static final String DECLARED = """
            data Forecast = { currency: String, amount: Int }

            let filed (cs: List<String>): Map<String, Int> =
                List.fold((acc, c) -> Map.updateOrInsert(c, 1, n -> n + 1, acc), Map.empty, cs)

            let totalsOf (fs: List<Forecast>): Map<String, Int> =
                List.fold((acc, f) -> Map.updateOrInsert(f.currency, f.amount,
                    n -> n + f.amount, acc), Map.empty, fs)

            """;

    private static final String HEAD = "module probe\n\n" + DECLARED + """
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
                "Map.size(Map.filterEntries((_, n) -> n > 0, totalsOf(fs)))",
                "Map.size(Map.filterEntries((_, n) -> n >= 2, filed(List.map(.currency, fs))))")) {
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
     * A value counted by what the elements under it come to may take more than one of them: a
     * currency held twice, or two amounts under one currency totalling nought where no amount is
     * nought. The rows composed for such a line hold as many as it takes, and answer as their
     * points say.
     */
    @Test
    void aValueIsComposedWithAsManyElementsUnderItAsWhatTheyComeToTakes() {
        everyRowComposedAnswersAsItsPointSays(DECLARED + """
                behavior f : (fs: List<Forecast>) -> Int
                let f (fs) = if Map.size(Map.filterEntries((_, n) -> n >= 2,
                    filed(List.map(.currency, fs)))) == 1 then 1 else 0
                """, "f/#different fs [fs[*].currency] where [multiplicity(fs[*].currency) >= 2]");
        everyRowComposedAnswersAsItsPointSays(DECLARED + """
                behavior f : (fs: List<Forecast>) -> Int
                let f (fs) = if List.all(f -> f.amount /= 0, fs) then
                    if Map.size(Map.filterEntries((_, n) -> n == 0, totalsOf(fs))) == 1 then 1
                    else 0
                    else 2
                """, "f/#different fs [fs[*].currency] where"
                + " [total(fs[*].amount by currency) == 0]");
    }

    /**
     * How often the value at a place inside an element occurs is a number of the element, and a
     * row at its line holds that value under as many elements as the line asks, chosen among the
     * values each element is read at whole.
     */
    @Test
    void howOftenAValueInsideAnElementOccursIsComposedWithThatManyElementsUnderIt() {
        everyRowComposedAnswersAsItsPointSays(DECLARED + """
                behavior f : (fs: List<Forecast>) -> Int
                let f (fs) = if Map.size(Map.filterEntries((_, n) -> n >= 2,
                    filed(List.map(.currency, fs)))) >= 1 then 1 else 0
                """, "f/multiplicity(fs[*].currency)");
    }

    /**
     * Elements meeting the statement may share a value: where every element is above nought and
     * one currency is counted, two elements are two of that currency. And a value some elements
     * must not hold is held by others where only they can hold it — two currencies kept and three
     * elements, one of them the `"x"` that only an element at or below nought is kept out at.
     */
    @Test
    void aLineUnderTheCountIsComposedWithElementsSharingAValueWhereItTakesThem() {
        everyRowComposedAnswersAsItsPointSays(DECLARED + """
                behavior f : (fs: List<Forecast>) -> Int
                let f (fs) = if List.all(f -> f.amount > 0, fs) then
                    if Set.size(Set.fromList(List.map(.currency,
                        List.filter(f -> f.amount > 0, fs)))) == 1 then
                        if List.length(fs) == 2 then 1 else 0
                    else 2
                    else 3
                """, "f/List.length(fs)", "0 <= List.length(fs) < 1");
        everyRowComposedAnswersAsItsPointSays(DECLARED + """
                behavior f : (fs: List<Forecast>) -> Int
                let f (fs) = if Set.size(Set.fromList(List.map(.currency,
                    List.filter(f -> f.currency /= "x" || f.amount > 0, fs)))) == 2 then
                    if List.length(fs) == 3 then 1 else 0
                    else 2
                """, "f/List.length(fs)", "0 <= List.length(fs) < 2");
    }

    /**
     * Asked of each value, a statement has to answer alike for every element holding it. Which of
     * them is the last to hold it reads no place but the value's, and answers differently for the
     * first and the last of them, so it is refused; whether the value is there at all is not.
     */
    @Test
    void aStatementTurningOnWhichElementHoldsAValueIsNoStatementOfEachValue() {
        DecisionSubject.AnInput fs = new DecisionSubject.AnInput(TermPath.of("fs"));
        DecisionSubject.AnInput currency = new DecisionSubject.AnInput(
                TermPath.of("fs").element().then("currency"));
        Quantity.HowManyDifferentMeet.Selection last =
                new Quantity.HowManyDifferentMeet.Selection.OfEachValue(
                        new Proposition.LastToHold(fs, currency, true, "last"));
        assertThrows(IllegalArgumentException.class,
                () -> new Quantity.HowManyDifferentMeet(fs, currency, last));
        assertNull(Quantity.HowManyDifferentMeet.of(fs, currency, last));
        assertNotNull(Quantity.HowManyDifferentMeet.of(fs, currency,
                new Quantity.HowManyDifferentMeet.Selection.OfEachValue(
                        new Proposition.Present(currency, true, "present"))));
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

    /**
     * A row this compiler composes for a point of a line answers what the point says, as the
     * language runs it: the rows of a line on {@code compared}, the last condition before the
     * answer is written, are each written as an example answering one above the line and nought
     * below it, and none of them is refused.
     *
     * <p>The rows themselves, and not examples written beside them: what a row is composed holding
     * is what is asked of it here, and a row the composer could not have built is never one an
     * example stands in for.
     *
     * @param behavior   a behavior {@code f} answering one where {@code compared} holds and nought
     *                   where it fails, under whatever conditions it is reached
     * @param outOfReach the points of the line no row reaches, by where each is, which are said to
     *                   have no row and never to have one composed
     */
    private static void everyRowComposedAnswersAsItsPointSays(String behavior, String compared,
                                                              String... outOfReach) {
        String source = "module probe\n\n" + behavior;
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        // Rendered at their places in the source, so the origin of one comparison is none of
        // another's.
        SourceRendering rendering = SourceRendering.namedByIdentity(compilation.texts());
        JsonNode report = JSON.readTree(AdequacyReport.of(compilation).json(rendering));
        JsonNode drawn = null;
        for (JsonNode each : behaviorOf(report).at("/partition/boundaries")) {
            if (compared.equals(each.path("axis").asString())) {
                drawn = each;
            }
        }
        assertTrue(drawn != null, () -> "a line on " + compared + ": " + report);
        for (JsonNode item : drawn.path("items")) {
            if (List.of(outOfReach).contains(item.path("against").asString())) {
                assertFalse(item.path("knownWritable").asBoolean(),
                        () -> "no row reaches " + item + ", and none is said to");
                continue;
            }
            assertTrue(item.has("notOwed") || item.path("knownWritable").asBoolean(),
                    () -> "a row is composed for every point of " + compared + ": " + item);
        }
        String origin = drawn.path("origin").asString();
        String rows = GeneratedRows.of(compilation, "probe", null, rendering).text();
        StringBuilder examples = new StringBuilder("\nexample f\n");
        List<String> said = new ArrayList<>();
        StringBuilder row = null;
        int written = 0;
        for (String line : rows.split("\n")) {
            if (line.startsWith("// fills ")) {
                said.add(line);
                continue;
            }
            if (line.startsWith("    |")) {
                row = new StringBuilder();
            }
            if (row == null) {
                continue;
            }
            row.append(line).append('\n');
            if (!line.contains("<?>")) {
                continue;
            }
            String answer = null;
            for (String fills : said) {
                if (fills.endsWith(" point of " + origin)) {
                    answer = fills.contains("fills ON ") || fills.contains("fills IN ") ? "1"
                            : "0";
                }
            }
            if (answer != null) {
                examples.append(row.toString().replace("<?>", answer));
                written++;
            }
            said.clear();
            row = null;
        }
        assertTrue(written > 0, () -> "rows composed for " + compared + ": " + rows);
        Compilation run = Compilation.ofSource(source + examples, "Main");
        run.measure(Adequacy.Asked.fullReport());
        run.answerEverything();
        assertEquals(List.of(), run.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList(),
                () -> "every row of " + compared + " answers as its point says:" + examples
                        + "\nout of the rows composed:\n" + rows);
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
