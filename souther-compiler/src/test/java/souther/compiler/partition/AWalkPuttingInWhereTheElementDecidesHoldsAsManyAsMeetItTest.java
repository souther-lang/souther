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
 * A walk whose step puts an element in where the element alone decides, and keeps what it carried
 * otherwise, holds as many as the elements meeting that: the rule over how many it holds comes to
 * what the rule over how many {@code List.filter} keeps comes to. What it carries is read as a
 * size and as a number by one reading, arm by arm, so a step that chooses on the element is read
 * the same whichever it is asked for. A choice made on what was carried is no statement about the
 * element, and the walk is not read so.
 *
 * <p>The filter is the oracle: each walk is judged beside it, and what each leaves unread has to
 * be the same, place for place and word for word.
 */
class AWalkPuttingInWhereTheElementDecidesHoldsAsManyAsMeetItTest {

    private static final String DECLARATIONS = """
            module probe

            data Item = { code: String, price: Int }
            data Prices = { known: Map<String, Int> }
            """;

    /** A rule over what the walk comes to, beside a rule the run gets to past the walk. */
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
                .map(each -> each.at() + "=" + each.reason()).toList()));
        return out;
    }

    @Test
    void aWalkPuttingInWhereTheElementDecidesHoldsAsManyAsMeetIt() {
        Map<String, String> judged = new LinkedHashMap<>();
        judged.put("filtered",
                "List.length(List.filter(i -> i.price > 0, items)) >= 0");
        judged.put("chosen", "List.length(List.fold((acc, i) -> "
                + "if i.price > 0 then acc ++ [i.price] else acc, [], items)) >= 0");
        judged.put("chosenTheOtherWay", "List.length(List.fold((acc, i) -> "
                + "if i.price <= 0 then acc else acc ++ [i.price], [], items)) >= 0");
        judged.put("decidedByWhatItCarried", "List.length(List.fold((acc, i) -> "
                + "if List.length(acc) < 3 then acc ++ [i.price] else acc, [], items)) >= 0");
        Map<String, List<String>> unread = unread(judged);

        for (String walk : List.of("chosen", "chosenTheOtherWay")) {
            assertEquals(unread.get("filtered"), unread.get(walk), walk);
        }
        assertTrue(unread.get("decidedByWhatItCarried").stream().anyMatch(each ->
                        each.endsWith("=" + UndividedPosition.Reason.RULE_MEASURED_ON_ITS_RUNS)),
                unread.get("decidedByWhatItCarried").toString());
    }
}
