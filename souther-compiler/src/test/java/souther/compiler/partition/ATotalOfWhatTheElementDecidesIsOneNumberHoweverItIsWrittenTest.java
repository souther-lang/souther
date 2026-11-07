package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

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
}
