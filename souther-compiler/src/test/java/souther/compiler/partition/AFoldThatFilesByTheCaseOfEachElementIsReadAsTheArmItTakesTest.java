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
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * A fold whose elements are of several cases, filing each under a key and a value its case says,
 * holds under a key what the law it files by makes of the elements of that key, each read as the
 * arm its case takes — however the choice is written: as the step's own {@code match}, as a
 * {@code match} for the key and one for the value, or as a map of the elements into what the fold
 * then files.
 *
 * <p>A receipt adds its quantity to what is on hand and an issue takes its quantity off, so the
 * figure under a sku is the total of the receipts' quantities less the issues', which no one field
 * of any element holds.
 */
class AFoldThatFilesByTheCaseOfEachElementIsReadAsTheArmItTakesTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String THE_STEPS_OWN_CHOICE = """
            List.fold((acc, m) -> match m with
                    | Receipt { sku, quantity } ->
                        Map.updateOrInsert(sku, quantity, on -> on + quantity, acc)
                    | Issue { sku, quantity } ->
                        Map.updateOrInsert(sku, 0 - quantity, on -> on - quantity, acc),
                Map.empty, ms)""";

    /** The step's own choice, written as a helper whose parameter the choice is over. */
    private static final String A_HELPERS_CHOICE = """
            List.fold((acc, m) -> applied(acc, m), Map.empty, ms)""";

    private static final String THE_HELPER = """

            let applied (running: Map<String, Int>, movement: Movement): Map<String, Int> =
                match movement with
                    | Receipt { sku, quantity } ->
                        Map.updateOrInsert(sku, quantity, on -> on + quantity, running)
                    | Issue { sku, quantity } ->
                        Map.updateOrInsert(sku, 0 - quantity, on -> on - quantity, running)
            """;

    private static final String A_CHOICE_FOR_THE_KEY_AND_ONE_FOR_THE_VALUE = """
            List.fold((acc, m) -> {
                    let sku = match m with
                        | Receipt { sku } -> sku
                        | Issue { sku } -> sku
                    let q = match m with
                        | Receipt { quantity } -> quantity
                        | Issue { quantity } -> 0 - quantity
                    Map.updateOrInsert(sku, q, on -> on + q, acc)
                }, Map.empty, ms)""";

    private static final String A_MAP_OF_THE_ELEMENTS = """
            List.fold((acc, p) -> {
                    let (sku, q) = p
                    Map.updateOrInsert(sku, q, on -> on + q, acc)
                }, Map.empty, List.map(m -> match m with
                    | Receipt { sku, quantity } -> (sku, quantity)
                    | Issue { sku, quantity } -> (sku, 0 - quantity), ms))""";

    private static final String THE_TOTAL = "total({when @Receipt then 1·@Receipt.quantity + 0"
            + " when @Issue then -1·@Issue.quantity + 0 | ms[*]} by when @Receipt then"
            + " @Receipt.sku when @Issue then @Issue.sku)";

    /** A model filing the movements by {@code fold}, asked which skus are below the limit. */
    private static String model(String fold, String more) {
        return """
                module example.inventory

                data Receipt = { sku: String, quantity: Int }
                data Issue = { sku: String, quantity: Int }
                data Movement = Receipt | Issue

                let onHand (ms: List<Movement>): Map<String, Int> =
                %s

                behavior short : (ms: List<Movement>, limit: Int) -> Map<String, Int>

                let short (ms, limit) = Map.filterEntries((_, on) -> on < limit, onHand(ms))
                %s""".formatted(fold.indent(4), more);
    }

    /** A model whose movements are counted as well, a stocktake putting what it counted in place
     *  of what was on hand, filed by {@code fold}. */
    private static String counted(String fold, String more) {
        return """
                module example.inventory

                data Receipt = { sku: String, quantity: Int }
                data Issue = { sku: String, quantity: Int }
                data Stocktake = { sku: String, counted: Int }
                data Movement = Receipt | Issue | Stocktake

                let onHand (ms: List<Movement>): Map<String, Int> =
                %s

                behavior short : (ms: List<Movement>, limit: Int) -> Map<String, Int>

                let short (ms, limit) = Map.filterEntries((_, on) -> on < limit, onHand(ms))
                %s""".formatted(fold.indent(4), more);
    }

    private static final String COUNTED = """
            List.fold((acc, m) -> match m with
                    | Receipt { sku, quantity } ->
                        Map.updateOrInsert(sku, quantity, on -> on + quantity, acc)
                    | Issue { sku, quantity } ->
                        Map.updateOrInsert(sku, 0 - quantity, on -> on - quantity, acc)
                    | Stocktake { sku, counted } -> Map.insert(sku, counted, acc),
                Map.empty, ms)""";

    /**
     * A stocktake puts what it counted in place of what was on hand, so what is on hand of a sku
     * is the total of its movements from the last stocktake of it: the line is on that total,
     * every point of it is owed, and the rows offered for it, run, meet it.
     */
    @Test
    void theLineOnTheTotalFromTheLastStocktakeIsOwedOfferedAndThenMet() {
        String examples = """

                example short
                    | "none" : ([], 0) -> []
                """;
        Compilation before = measured(counted(COUNTED, examples));
        assertTrue(json(before).contains("total_from_the_last_put"), () -> report(before));
        assertTrue(axisOf(before).getFirst().contains("from the last @Stocktake"),
                () -> report(before));
        assertEquals(List.of("ON", "OFF", "IN", "OUT"), unmetOf(before),
                () -> "every point of the line is owed: " + report(before));
        List<Row> offered = offeredRows(before);
        assertFalse(offered.isEmpty(), () -> "rows are offered: " + report(before));
        StringBuilder written = new StringBuilder(examples);
        int named = 0;
        for (Row row : offered) {
            written.append("    | \"offered ").append(named++).append("\" : (")
                    .append(row.written()).append(") -> ").append(entries(row.shortOf()))
                    .append("\n");
        }
        Compilation after = measured(counted(COUNTED, written.toString()));
        assertEquals(List.of(), unmetOf(after),
                () -> "the rows that were offered meet the line: " + report(after));
    }

    /**
     * What the movements before the last stocktake added is gone from what is on hand: five
     * received, two counted and three issued is one short, which is on the line at nought, and
     * neither the total of all three nor the last one alone is.
     */
    @Test
    void aStocktakePutsWhatItCountedInPlaceOfEveryMovementBeforeIt() {
        Row row = new Row(List.of(new Movement("Receipt", "a", 5),
                new Movement("Stocktake", "a", 2), new Movement("Issue", "a", 3)), 0);
        assertEquals(Map.of("a", -1), row.shortOf());
        Compilation compilation = measured(counted(COUNTED, """

                example short
                    | "counted between" : (%s) -> %s
                """.formatted(row.written(), entries(row.shortOf()))));
        assertFalse(unmetOf(compilation).contains("ON"),
                () -> "one short is on the line: " + report(compilation));
    }

    /** The lines are written in a document the schema shipped beside this accepts. */
    @Test
    void theDocumentsNamingTheseTotalsAreOnesTheSchemaAccepts() {
        DocumentShape.assertShapedLikeTheSchema(JSON.readTree(json(measured(
                model(THE_STEPS_OWN_CHOICE, "")))));
        DocumentShape.assertShapedLikeTheSchema(JSON.readTree(json(measured(
                counted(COUNTED, "")))));
    }

    /** Which stocktake was the last is the order the walk hands the movements in, and a walk
     *  from the end of the list hands the last of them first. */
    @Test
    void aWalkFromTheEndReadsNoLastStocktake() {
        Compilation compilation = measured(counted(COUNTED
                .replace("List.fold((acc, m)", "List.foldRight((m, acc)")
                .replace("Map.empty, ms)", "nothing(), ms)"), """

                let nothing : Map<String, Int> = Map.empty
                """));
        assertFalse(json(compilation).contains("total_from_the_last_put"),
                () -> report(compilation));
        assertTrue(report(compilation).contains("not read"), () -> report(compilation));
    }

    /** One movement of an offered row: which case it is, its sku and its quantity. */
    private record Movement(String kind, String sku, int quantity) {

        /** The field the case holds its quantity at. */
        String field() {
            return kind.equals("Stocktake") ? "counted" : "quantity";
        }
    }

    /** One row offered for {@code short}: the movements, in order, and the limit. */
    private record Row(List<Movement> movements, int limit) {

        /** What is on hand of each sku below the limit, in the order the skus first occur: a
         *  receipt adds, an issue takes off, and a stocktake puts what it counted. */
        Map<String, Integer> shortOf() {
            Map<String, Integer> onHand = new LinkedHashMap<>();
            for (Movement each : movements) {
                switch (each.kind()) {
                    case "Receipt" -> onHand.merge(each.sku(), each.quantity(), Integer::sum);
                    case "Issue" -> onHand.merge(each.sku(), -each.quantity(), Integer::sum);
                    default -> onHand.put(each.sku(), each.quantity());
                }
            }
            Map<String, Integer> out = new LinkedHashMap<>();
            onHand.forEach((sku, on) -> {
                if (on < limit) {
                    out.put(sku, on);
                }
            });
            return out;
        }

        String written() {
            List<String> each = new ArrayList<>();
            for (Movement movement : movements) {
                each.add(movement.kind() + " { sku = \"" + movement.sku() + "\", "
                        + movement.field() + " = " + movement.quantity() + " }");
            }
            return each + ", " + limit;
        }
    }

    /** Each way of writing the choice is the one total, and the line is on it. */
    @Test
    void everyWayOfWritingTheChoiceIsTheOneTotal() {
        Compilation stepped = measured(model(THE_STEPS_OWN_CHOICE, ""));
        List<String> line = axisOf(stepped);
        assertEquals(1, line.size(), () -> "one line: " + report(stepped));
        assertTrue(line.getFirst().contains(THE_TOTAL), () -> "the line is on " + THE_TOTAL
                + ": " + report(stepped));
        for (String fold : List.of(A_CHOICE_FOR_THE_KEY_AND_ONE_FOR_THE_VALUE,
                A_MAP_OF_THE_ELEMENTS)) {
            Compilation compilation = measured(model(fold, ""));
            assertEquals(line, axisOf(compilation), () -> fold + ": " + report(compilation));
        }
        Compilation helped = measured(model(A_HELPERS_CHOICE, THE_HELPER));
        assertEquals(line, axisOf(helped), () -> "a helper's choice: " + report(helped));
    }

    /** Every point of the line is owed, and the rows offered for it, run, meet it. */
    @Test
    void theLineOnTheTotalIsOwedOfferedAndThenMet() {
        String examples = """

                example short
                    | "none" : ([], 0) -> []
                """;
        Compilation before = measured(model(THE_STEPS_OWN_CHOICE, examples));
        assertEquals(List.of("ON", "OFF", "IN", "OUT"), unmetOf(before),
                () -> "every point of the line is owed: " + report(before));
        List<Row> offered = offeredRows(before);
        assertFalse(offered.isEmpty(), () -> "rows are offered: " + report(before));
        assertTrue(offered.stream().anyMatch(row -> row.movements().stream()
                        .anyMatch(each -> each.kind().equals("Issue"))),
                () -> "some row is met by an issue: " + offered);
        StringBuilder written = new StringBuilder(examples);
        int named = 0;
        for (Row row : offered) {
            written.append("    | \"offered ").append(named++).append("\" : (")
                    .append(row.written()).append(") -> ").append(entries(row.shortOf()))
                    .append("\n");
        }
        Compilation after = measured(model(THE_STEPS_OWN_CHOICE, written.toString()));
        assertEquals(List.of(), unmetOf(after),
                () -> "the rows that were offered meet the line: " + report(after));
    }

    /**
     * A choice whose arms file by unlike laws makes no one law of the elements of a key: an arm
     * putting a figure read of what was filed so far, a counter moving by another step on each
     * arm, or an arm keeping the less of two. Nor does one whose arms are chosen by what was filed
     * so far.
     */
    @Test
    void armsFilingByUnlikeLawsOrChosenByTheAnswerSoFarAreNotReadAsATotal() {
        for (String fold : List.of("""
                List.fold((acc, m) -> match m with
                        | Receipt { sku, quantity } ->
                            Map.updateOrInsert(sku, quantity, on -> on + quantity, acc)
                        | Issue { sku } -> Map.insert(sku, Map.size(acc), acc),
                    Map.empty, ms)""", """
                List.fold((acc, m) -> match m with
                        | Receipt { sku } -> Map.updateOrInsert(sku, 1, on -> on + 1, acc)
                        | Issue { sku } -> Map.updateOrInsert(sku, 1, on -> on + 2, acc),
                    Map.empty, ms)""", """
                List.fold((acc, m) -> match m with
                        | Receipt { sku, quantity } ->
                            Map.updateOrInsert(sku, quantity, on -> on + quantity, acc)
                        | Issue { sku, quantity } ->
                            Map.updateOrInsert(sku, quantity, on -> Int.min(on, quantity), acc),
                    Map.empty, ms)""", """
                List.fold((acc, m) -> {
                        let sku = match m with
                            | Receipt { sku } -> sku
                            | Issue { sku } -> sku
                        match Map.get(sku, acc) with
                            | Some seen -> Map.updateOrInsert("again", seen, on -> on + 1, acc)
                            | None -> Map.updateOrInsert(sku, 1, on -> on + 1, acc)
                    }, Map.empty, ms)""")) {
            Compilation compilation = measured(model(fold, ""));
            assertFalse(json(compilation).contains("total(")
                            || json(compilation).contains("multiplicity("),
                    () -> fold + ": " + report(compilation));
            assertTrue(report(compilation).contains("not read"), () -> fold + ": "
                    + report(compilation));
        }
    }

    private static String entries(Map<String, Integer> kept) {
        List<String> each = new ArrayList<>();
        kept.forEach((key, value) -> each.add("(\"" + key + "\", " + value + ")"));
        return each.toString();
    }

    private static final Pattern ROW = Pattern.compile("^\\[(.*)\\], (-?\\d+)$");

    private static final Pattern MOVEMENT = Pattern.compile("(Receipt|Issue|Stocktake)"
            + " \\{ sku = \"((?:[^\"\\\\]|\\\\.)*)\", (?:quantity|counted) = (-?\\d+) \\}");

    /** Every row the block offers, read back from how it is written; a row this cannot read back
     *  whole fails, since a part left unread is one nothing checks. */
    private static List<Row> offeredRows(Compilation compilation) {
        List<Row> out = new ArrayList<>();
        for (String each : Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("example.inventory"))
                .rowsByBehavior().getOrDefault("short", List.of()).stream()
                .map(row -> String.join(", ",
                        row.inputs().stream().map(FixtureTemplate::text).toList()))
                .toList()) {
            Matcher matched = ROW.matcher(each);
            if (!matched.matches()) {
                fail("an offered row is one this reads back: " + each);
            }
            List<Movement> movements = new ArrayList<>();
            Matcher one = MOVEMENT.matcher(matched.group(1));
            StringBuilder rest = new StringBuilder();
            while (one.find()) {
                movements.add(new Movement(one.group(1), one.group(2),
                        Integer.parseInt(one.group(3))));
                one.appendReplacement(rest, "");
            }
            one.appendTail(rest);
            if (!rest.toString().replace(",", "").isBlank()) {
                fail("the movements of an offered row are read to the end: " + each);
            }
            out.add(new Row(movements, Integer.parseInt(matched.group(2))));
        }
        return out;
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

    /** The quantity each border is on, as the report names it, and the value it is drawn at. */
    private static List<String> axisOf(Compilation compilation) {
        List<JsonNode> borders = new ArrayList<>();
        collect(JSON.readTree(json(compilation)), borders);
        return borders.stream()
                .map(each -> each.path("axis").asString() + " " + each.path("value").asString())
                .toList();
    }

    private static void collect(JsonNode node, List<JsonNode> out) {
        if (node.isObject() && node.has("items") && node.has("axis")) {
            out.add(node);
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
