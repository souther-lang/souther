package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

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

    /** What each of {@code judged} leaves unread, by the behavior's name. */
    private static Map<String, List<String>> unread(Map<String, String> judged) {
        StringBuilder source = new StringBuilder(DECLARATIONS);
        judged.forEach((name, rule) -> source.append(JUDGED.formatted(name, rule)));
        Compilation compilation = Compilation.ofSource(source.toString(), "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        Map<String, PartitionEvidence> evidence =
                compilation.db().ask(new Adequacy.Coverage("probe")).value();
        // A body that does not type is no body read, and leaves nothing unread.
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the models under test compile");
        Map<String, List<String>> out = new LinkedHashMap<>();
        judged.keySet().forEach(name -> out.put(name, evidence.get(name).notRead().stream()
                .filter(each -> !OF_THE_RULE_PAST_IT.contains(each.at()))
                .map(each -> each.at() + "=" + each.reason()).toList()));
        return out;
    }

    /** The places the rule past the total reads, which a run gets to only past the total. */
    private static final List<String> OF_THE_RULE_PAST_IT =
            List.of("items[*].code", "prices.known[key]");

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
     * test however its sides are written. Filters and takes stacked are their tests together. A
     * walk numbering what a filter kept, and a take of what a filter kept, count positions that
     * are none of the list's, and a filter of what a walk answered tests the answer and not the
     * element: all three stay unread.
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
        Map<String, List<String>> unread = unread(judged);

        assertTrue(unread.get("comparedSummed").contains(
                        "List.sum({if 1·price + -10 > 0 then 1·price + 0 else 0 | items[*]})="
                                + UndividedPosition.Reason.RULE_ABOUT_A_RUN),
                unread.get("comparedSummed").toString());
        assertTrue(unread.get("counted").stream().noneMatch(each ->
                        each.startsWith("items=") || each.startsWith("items[*].price=")),
                unread.get("counted").toString());
        Map<String, List<String>> ways = Map.of(
                "flagSummed", List.of("flagFiltered", "flagFoldFiltered"),
                "comparedSummed", List.of("comparedInTheStep", "comparedFiltered",
                        "comparedTheOtherWay", "comparedScaled"),
                "chosenTwice", List.of("filteredTwice"),
                "chosenOfATake", List.of("filteredOfATake", "foldOfAFilteredTake"),
                "counted", List.of("countedBySumming", "countedThroughTheFilter",
                        "countedByAFoldOfTheFilter"));
        ways.forEach((oracle, others) -> others.forEach(way ->
                assertEquals(unread.get(oracle), unread.get(way), way)));
        for (String control : List.of("aTakeOfWhatAFilterKept", "numberingWhatAFilterKept",
                "aFilterOfWhatAWalkAnswered")) {
            assertTrue(unread.get(control).stream().anyMatch(each ->
                            each.startsWith("items[*].price=")),
                    control + " " + unread.get(control));
        }
    }

    /** A choice by a comparison is written in the report as the schema says one is. */
    @Test
    void aChoiceByAComparisonIsWrittenTheWayTheSchemaSays() {
        Compilation compilation = Compilation.ofSource(DECLARATIONS + JUDGED.formatted("compared",
                "List.sum(List.map(i -> i.price, List.filter(i -> i.price > 10, items))) >= 0"),
                "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        JsonNode document = JsonMapper.builder().build().readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        DocumentShape.assertShapedLikeTheSchema(document);
        assertTrue(document.findValues("kind").stream()
                        .anyMatch(kind -> kind.asString("").equals("compared")),
                document.toString());
    }
}
