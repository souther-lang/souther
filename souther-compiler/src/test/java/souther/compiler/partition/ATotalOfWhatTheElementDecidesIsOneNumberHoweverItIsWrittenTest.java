package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.ACompiledModel;
import souther.compiler.DocumentShape;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A total of what each element adds where the element alone decides how much is one number however
 * it is written: a walk choosing in its step, a walk adding a choice, and a sum of what a closure
 * chooses. A total adding a number of the element is the total of the choice over the run; one
 * adding only numbers written out counts the elements meeting the choice, as a count of what a
 * filter keeps does. A choice made on what the walk carried, or an arm doing more to it than add,
 * is no such total.
 *
 * <p>Each way is judged beside one oracle, word for word, and the oracle is held to what it reads
 * as.
 */
class ATotalOfWhatTheElementDecidesIsOneNumberHoweverItIsWrittenTest {

    private static final String DECLARATIONS = """
            module probe

            data Item = { code: String, price: Int, active: Bool }
            data Prices = { known: Map<String, Int> }
            """;

    /** A rule over what the total comes to, beside a rule the run gets to past it. */
    private static final String JUDGED = """

            behavior %1$s : (items: List<Item>, prices: Prices) -> Bool
            let %1$s (items, prices) = {
                %2$s
                    && List.all(i -> Map.containsKey(i.code, prices.known), items)
            }
            """;

    /** What each of {@code judged} leaves unread, by the behavior's name: of the total, and of
     *  the rule past it. */
    private static Map<String, List<String>> unread(Map<String, String> judged) {
        StringBuilder source = new StringBuilder(DECLARATIONS);
        judged.forEach((name, rule) -> source.append(JUDGED.formatted(name, rule)));
        Compilation compilation = Compilation.ofSource(source.toString(), "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        Map<String, PartitionEvidence> evidence =
                compilation.db().ask(new Adequacy.Coverage("probe")).value();
        Map<String, List<String>> out = new LinkedHashMap<>();
        judged.keySet().forEach(name -> out.put(name, evidence.get(name).notRead().stream()
                .map(each -> each.at() + "=" + each.reason()).sorted().toList()));
        // A body that does not type is no body read, and leaves nothing unread.
        ACompiledModel.compiles(compilation);
        return out;
    }

    /** What {@code unread} says of the places the rule past the total reads, which a run gets to
     *  only past the total. */
    private static List<String> ofTheRulePastIt(List<String> unread) {
        return unread.stream().filter(each -> each.startsWith("items[*].code=")
                || each.startsWith("prices.known[key]=")).toList();
    }

    /**
     * The rule past a total is reached as it is past {@code List.sum} of the prices, however the
     * total is written: a fold adding in its step, a total of a choice, a count by a filter, by a
     * sum or by a fold. A run walking one element gets past each of them at every value the rule
     * reads — the step applied once, to the seed — and a count is an {@code Int} however many
     * elements meet. A step that stops on the code the rule reads is no such total, written as a
     * fold or as a sum of what each element answers.
     */
    @Test
    void theRulePastATotalIsReachedHoweverTheTotalIsWritten() {
        Map<String, String> judged = new LinkedHashMap<>();
        judged.put("summed", "List.sum(List.map(i -> i.price, items)) >= 0");
        judged.put("folded", "List.fold((acc, i) -> acc + i.price, 0, items) >= 0");
        judged.put("aChoiceSummed",
                "List.sum(List.map(i -> if i.active then i.price else 0, items)) >= 0");
        judged.put("aChoiceInTheStep", "List.fold((acc, i) -> "
                + "if i.active then acc + i.price else acc, 0, items) >= 0");
        judged.put("aComparisonSummed",
                "List.sum(List.map(i -> if i.price > 10 then i.price else 0, items)) >= 0");
        judged.put("counted", "List.length(List.filter(i -> i.active, items)) >= 1");
        judged.put("countedBySumming",
                "List.sum(List.map(i -> if i.active then 1 else 0, items)) >= 1");
        judged.put("countedInTheStep", "List.fold((acc, i) -> "
                + "if i.active then acc + 1 else acc, 0, items) >= 1");
        judged.put("countedByAFold", "List.fold((acc, i) -> acc + 1, 0, items) >= 1");
        judged.put("stoppingOnTheCodeInTheStep", "List.fold((acc, i) -> "
                + "acc + Int.floorMod(10, String.length(i.code)), 0, items) >= 0");
        judged.put("stoppingOnTheCodeSummed", "List.sum(List.map(i -> "
                + "Int.floorMod(10, String.length(i.code)), items)) >= 0");
        Map<String, List<String>> unread = unread(judged);

        List<String> oracle = ofTheRulePastIt(unread.get("summed"));
        assertEquals(List.of("items[*].code=" + UndividedPosition.Reason.RULE_RELATING_TWO_VALUES,
                "prices.known[key]=" + UndividedPosition.Reason.RULE_RELATING_TWO_VALUES), oracle);
        for (String way : List.of("folded", "aChoiceSummed", "aChoiceInTheStep",
                "aComparisonSummed", "counted", "countedBySumming", "countedInTheStep",
                "countedByAFold")) {
            assertEquals(oracle, ofTheRulePastIt(unread.get(way)), way);
        }
        for (String control : List.of("stoppingOnTheCodeInTheStep", "stoppingOnTheCodeSummed")) {
            assertTrue(ofTheRulePastIt(unread.get(control)).stream().noneMatch(each ->
                            each.equals("items[*].code="
                                    + UndividedPosition.Reason.RULE_RELATING_TWO_VALUES)),
                    control + " " + unread.get(control));
        }
    }

    @Test
    void aTotalOfWhatTheElementDecidesIsOneNumberHoweverItIsWritten() {
        Map<String, String> judged = new LinkedHashMap<>();
        judged.put("summed", "List.sum(List.map(i -> if i.active then i.price else 0, items)) >= 0");
        judged.put("chosenInTheStep", "List.fold((acc, i) -> "
                + "if i.active then acc + i.price else acc, 0, items) >= 0");
        judged.put("aChoiceAdded", "List.fold((acc, i) -> "
                + "acc + (if i.active then i.price else 0), 0, items) >= 0");
        judged.put("summedTheOtherWay",
                "List.sum(List.map(i -> if i.active then 0 else i.price, items)) >= 0");
        judged.put("chosenTheOtherWay", "List.fold((acc, i) -> "
                + "if i.active then acc else acc + i.price, 0, items) >= 0");
        judged.put("counted", "2 * List.length(List.filter(i -> i.active, items)) >= 1");
        judged.put("countedBySumming",
                "List.sum(List.map(i -> if i.active then 2 else 0, items)) >= 1");
        judged.put("countedInTheStep", "List.fold((acc, i) -> "
                + "if i.active then acc + 2 else acc, 0, items) >= 1");
        judged.put("decidedByWhatItCarried", "List.fold((acc, i) -> "
                + "if acc > 100 then acc else acc + i.price, 0, items) >= 0");
        judged.put("anArmDoublingWhatItCarried", "List.fold((acc, i) -> "
                + "if i.active then acc + acc + i.price else acc, 0, items) >= 0");
        Map<String, List<String>> unread = unread(judged);

        assertTrue(unread.get("summed").contains(
                        "List.sum({if active then 1·price + 0 else 0 | items[*]})="
                                + UndividedPosition.Reason.RULE_ABOUT_A_RUN),
                unread.get("summed").toString());
        assertTrue(unread.get("counted").stream().noneMatch(each ->
                        each.startsWith("items=") || each.startsWith("items[*].active=")),
                unread.get("counted").toString());
        for (String way : List.of("chosenInTheStep", "aChoiceAdded")) {
            assertEquals(unread.get("summed"), unread.get(way), way);
        }
        assertEquals(unread.get("summedTheOtherWay"), unread.get("chosenTheOtherWay"));
        for (String way : List.of("countedBySumming", "countedInTheStep")) {
            assertEquals(unread.get("counted"), unread.get(way), way);
        }
        for (String control : List.of("decidedByWhatItCarried", "anArmDoublingWhatItCarried")) {
            assertTrue(unread.get(control).contains("items[*].price="
                            + UndividedPosition.Reason.RULE_MEASURED_ON_ITS_RUNS),
                    control + " " + unread.get(control));
        }
    }

    /**
     * A total of what a filter keeps is the total of every element counting nought where the
     * filter's closure fails, and a comparison of the element's numbers chooses as a flag does:
     * each way of writing one of them is the choice summed, word for word, and a comparison is one
     * test however its sides are written. Filters and takes stacked are their tests together, and
     * a filter of what a walk answered is the filter of the elements by what the walk answered of
     * each. A walk numbering what a filter kept, a take of what a filter kept, and a filter of
     * what a walk numbered count positions that are none of the list's, and stay unread.
     */
    @Test
    void aTotalOfWhatAFilterOrAComparisonKeepsIsTheChoiceSummed() {
        Map<String, String> judged = new LinkedHashMap<>();
        judged.put("flagSummed",
                "List.sum(List.map(i -> if i.active then i.price else 0, items)) >= 0");
        judged.put("flagFiltered", "List.sum(List.map(i -> i.price, "
                + "List.filter(i -> i.active, items))) >= 0");
        judged.put("flagFoldFiltered", "List.fold((acc, i) -> acc + i.price, 0, "
                + "List.filter(i -> i.active, items)) >= 0");
        judged.put("comparedSummed",
                "List.sum(List.map(i -> if i.price > 10 then i.price else 0, items)) >= 0");
        judged.put("comparedInTheStep", "List.fold((acc, i) -> "
                + "if i.price > 10 then acc + i.price else acc, 0, items) >= 0");
        judged.put("comparedFiltered", "List.sum(List.map(i -> i.price, "
                + "List.filter(i -> i.price > 10, items))) >= 0");
        judged.put("comparedTheOtherWay", "List.sum(List.map(i -> i.price, "
                + "List.filter(i -> 10 < i.price, items))) >= 0");
        judged.put("comparedScaled", "List.sum(List.map(i -> i.price, "
                + "List.filter(i -> 2 * i.price - 20 > 0, items))) >= 0");
        judged.put("comparedTheDeniedWay",
                "List.sum(List.map(i -> if i.price <= 10 then 0 else i.price, items)) >= 0");
        judged.put("chosenTwice", "List.sum(List.map(i -> "
                + "if i.price > 10 then (if i.active then i.price else 0) else 0, items)) >= 0");
        judged.put("filteredTwice", "List.sum(List.map(i -> i.price, List.filter(i -> i.active, "
                + "List.filter(i -> i.price > 10, items)))) >= 0");
        judged.put("chosenOfATake", "List.sum(List.map(i -> if i.active then i.price else 0, "
                + "List.take(2, items))) >= 0");
        judged.put("filteredOfATake", "List.sum(List.map(i -> i.price, "
                + "List.filter(i -> i.active, List.take(2, items)))) >= 0");
        judged.put("foldOfAFilteredTake", "List.fold((acc, i) -> acc + i.price, 0, "
                + "List.filter(i -> i.active, List.take(2, items))) >= 0");
        judged.put("counted", "List.length(List.filter(i -> i.price > 10, items)) >= 1");
        judged.put("countedBySumming",
                "List.sum(List.map(i -> if i.price > 10 then 1 else 0, items)) >= 1");
        judged.put("countedThroughTheFilter",
                "List.sum(List.map(i -> 1, List.filter(i -> i.price > 10, items))) >= 1");
        judged.put("countedByAFoldOfTheFilter", "List.fold((acc, i) -> acc + 1, 0, "
                + "List.filter(i -> i.price > 10, items)) >= 1");
        judged.put("aTakeOfWhatAFilterKept", "List.sum(List.map(i -> i.price, "
                + "List.take(2, List.filter(i -> i.active, items)))) >= 0");
        judged.put("numberingWhatAFilterKept", "List.sum(List.mapIndexed((k, i) -> "
                + "if k == 0 then i.price else 0, List.filter(i -> i.active, items))) >= 0");
        judged.put("aFilterOfWhatAWalkAnswered", "List.sum(List.filter(p -> p > 10, "
                + "List.map(i -> i.price, items))) >= 0");
        judged.put("aFoldOfWhatAWalkAnsweredFiltered", "List.fold((acc, p) -> acc + p, 0, "
                + "List.filter(p -> p > 10, List.map(i -> i.price, items))) >= 0");
        judged.put("doubledChosen",
                "List.sum(List.map(i -> if i.price > 10 then 2 * i.price else 0, items)) >= 0");
        judged.put("doubledOfWhatAWalkAnsweredFiltered", "List.sum(List.map(p -> 2 * p, "
                + "List.filter(p -> p > 10, List.map(i -> i.price, items)))) >= 0");
        judged.put("doubled", "List.sum(List.map(i -> 2 * i.price, items)) >= 0");
        judged.put("doubledOfWhatAWalkAnswered", "List.sum(List.map(p -> 2 * p, "
                + "List.map(i -> i.price, items))) >= 0");
        judged.put("aFoldDoublingWhatAWalkAnswered", "List.fold((acc, p) -> acc + 2 * p, 0, "
                + "List.map(i -> i.price, items)) >= 0");
        judged.put("byTheCode",
                "List.sum(List.map(i -> if i.code == \"A\" then i.price else 0, items)) >= 0");
        judged.put("byTheCodeFiltered", "List.sum(List.map(i -> i.price, "
                + "List.filter(i -> \"A\" == i.code, items))) >= 0");
        judged.put("byAnotherCode", "List.fold((acc, i) -> "
                + "if i.code /= \"A\" then acc else acc + i.price, 0, items) >= 0");
        judged.put("countedByTheCode", "List.length(List.filter(i -> i.code == \"A\", items)) >= 1");
        judged.put("countedByTheCodeSummed",
                "List.sum(List.map(i -> if i.code == \"A\" then 1 else 0, items)) >= 1");
        judged.put("aFilterOfWhereAWalkNumbered", "List.sum(List.filter(p -> p > 10, "
                + "List.mapIndexed((k, i) -> k + i.price, items))) >= 0");
        Map<String, List<String>> unread = unread(judged);

        assertTrue(unread.get("comparedSummed").contains(
                        "List.sum({if 1·price + -10 > 0 then 1·price + 0 else 0 | items[*]})="
                                + UndividedPosition.Reason.RULE_ABOUT_A_RUN),
                unread.get("comparedSummed").toString());
        assertTrue(unread.get("byTheCode").contains(
                        "List.sum({if code == \"A\" then 1·price + 0 else 0 | items[*]})="
                                + UndividedPosition.Reason.RULE_ABOUT_A_RUN),
                unread.get("byTheCode").toString());
        assertTrue(unread.get("counted").stream().noneMatch(each ->
                        each.startsWith("items=") || each.startsWith("items[*].price=")),
                unread.get("counted").toString());
        Map<String, List<String>> ways = Map.of(
                "flagSummed", List.of("flagFiltered", "flagFoldFiltered"),
                "comparedSummed", List.of("comparedInTheStep", "comparedFiltered",
                        "comparedTheOtherWay", "comparedScaled", "comparedTheDeniedWay",
                        "aFilterOfWhatAWalkAnswered",
                        "aFoldOfWhatAWalkAnsweredFiltered"),
                "doubledChosen", List.of("doubledOfWhatAWalkAnsweredFiltered"),
                "doubled", List.of("doubledOfWhatAWalkAnswered", "aFoldDoublingWhatAWalkAnswered"),
                "byTheCode", List.of("byTheCodeFiltered", "byAnotherCode"),
                "countedByTheCode", List.of("countedByTheCodeSummed"),
                "chosenTwice", List.of("filteredTwice"),
                "chosenOfATake", List.of("filteredOfATake", "foldOfAFilteredTake"),
                "counted", List.of("countedBySumming", "countedThroughTheFilter",
                        "countedByAFoldOfTheFilter"));
        ways.forEach((oracle, others) -> others.forEach(way ->
                assertEquals(unread.get(oracle), unread.get(way), way)));
        for (String control : List.of("aTakeOfWhatAFilterKept", "numberingWhatAFilterKept",
                "aFilterOfWhereAWalkNumbered")) {
            assertTrue(unread.get(control).stream().anyMatch(each ->
                            each.startsWith("items[*].price=")),
                    control + " " + unread.get(control));
        }
    }

    /**
     * A count of the elements meeting a test is met by the element the rule past it reads only
     * where the test reads nothing the rule reads. A list of one element whose price passes ten
     * reaches a rule over the price at no price of ten or less, and a list of one whose flag is
     * set reaches it at every price.
     */
    @Test
    void anElementMeetingWhatIsCountedIsTheOneTheRuleReadsOnlyApartFromWhatTheRuleReads() {
        String declarations = """
                module probe

                data Item = { code: String, price: Int, active: Bool }
                data Prices = { cap: Int }
                """;
        String judged = """

                behavior %1$s : (items: List<Item>, prices: Prices) -> Bool
                let %1$s (items, prices) = {
                    List.length(items) <= 1
                        && List.fold((acc, i) -> if %2$s then acc + 1 else acc, 0, items) >= 1
                        && List.all(i -> i.price <= prices.cap, items)
                }
                """;
        Map<String, String> tests = Map.of("byThePrice", "i.price > 10", "byTheFlag", "i.active");
        StringBuilder source = new StringBuilder(declarations);
        tests.forEach((name, test) -> source.append(judged.formatted(name, test)));
        Compilation compilation = Compilation.ofSource(source.toString(), "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        Map<String, PartitionEvidence> evidence =
                compilation.db().ask(new Adequacy.Coverage("probe")).value();
        String reached = "items[*].price=" + UndividedPosition.Reason.RULE_RELATING_TWO_VALUES;
        Map<String, List<String>> unread = new LinkedHashMap<>();
        tests.keySet().forEach(name -> unread.put(name, evidence.get(name).notRead().stream()
                .map(each -> each.at() + "=" + each.reason()).toList()));
        assertTrue(unread.get("byTheFlag").contains(reached), unread.toString());
        assertTrue(unread.get("byThePrice").stream().noneMatch(reached::equals),
                unread.toString());
        ACompiledModel.compiles(compilation);
    }

    /**
     * A total of numbers the elements hold is past an {@code Int} on some runs, where a count is
     * not: two elements priced at the cap add up past one where the cap is past half of one, and
     * a rule past their total is not reached there. Two elements counted are two however they are
     * priced.
     */
    @Test
    void aTotalOfWhatTheElementsHoldIsNoIntOnEveryRunWhereACountIs() {
        String declarations = """
                module probe

                data Item = { code: String, price: Int, active: Bool }
                data Prices = { cap: Int, other: Int }
                """;
        String judged = """

                behavior %1$s : (items: List<Item>, prices: Prices) -> Bool
                let %1$s (items, prices) = {
                    List.length(items) == 2
                        && List.all(i -> i.price == prices.cap, items)
                        && %2$s >= 0
                        && prices.cap <= prices.other
                }
                """;
        Map<String, String> totals = Map.of(
                "priced", "List.sum(List.map(i -> i.price, items))",
                "counted", "List.sum(List.map(i -> if i.active then 1 else 0, items))");
        StringBuilder source = new StringBuilder(declarations);
        totals.forEach((name, total) -> source.append(judged.formatted(name, total)));
        Compilation compilation = Compilation.ofSource(source.toString(), "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        Map<String, PartitionEvidence> evidence =
                compilation.db().ask(new Adequacy.Coverage("probe")).value();
        String notReached = "prices.cap="
                + UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE;
        Map<String, List<String>> unread = new LinkedHashMap<>();
        totals.keySet().forEach(name -> unread.put(name, evidence.get(name).notRead().stream()
                .map(each -> each.at() + "=" + each.reason()).toList()));
        assertTrue(unread.get("priced").contains(notReached), unread.toString());
        assertTrue(unread.get("counted").stream().noneMatch(notReached::equals),
                unread.toString());
        ACompiledModel.compiles(compilation);
    }

    /** A choice by a comparison, and one by a string written out, is written in the report as the
     *  schema says one is. */
    @Test
    void aChoiceByAComparisonIsWrittenTheWayTheSchemaSays() {
        Map<String, String> kinds = Map.of(
                "compared", "List.filter(i -> i.price > 10, items)",
                "written", "List.filter(i -> i.code == \"A\", items)");
        kinds.forEach((kind, kept) -> {
            Compilation compilation = ACompiledModel.measured(DECLARATIONS + JUDGED.formatted(kind,
                    "List.sum(List.map(i -> i.price, " + kept + ")) >= 0"),
                    Adequacy.Asked.fullReport());
            JsonNode document = JsonMapper.builder().build().readTree(
                    AdequacyReport.of(compilation)
                            .json(SourceRendering.namedByIdentity(compilation.texts())));
            DocumentShape.assertShapedLikeTheSchema(document);
            assertTrue(document.findValues("kind").stream()
                            .anyMatch(each -> each.asString("").equals(kind)),
                    kind + " " + document);
        });
    }
}
