package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * How many elements of a container meet a statement, held against another number, is shown to
 * reach every value the other number stands at wherever a row shows it: one element the statement
 * holds of and one it fails of, beside one value of everything else the behavior takes, at a row
 * that gets to the comparison. No row of the model is needed for it, since the rows are looked
 * for among what the types tell apart — the values of the places the statement reads, and a
 * collection it reads a place in holding one of what it holds.
 *
 * <p>Where no such row exists the count is not shown to reach, and the relation stays unread:
 * a statement no element meets, and a container whose rules cap how many it holds, which the
 * count's values past it are no row of.
 */
class ACountOfElementsThatMeetAStatementReachesWhatItIsHeldAgainstTest {

    private static final String DECLARATIONS = """
            module probe

            data Cur = String
                invariant String.matches("[A-Z]{3}", value)
            data Line = { currency: Cur, flag: Bool }
            data Capped = { items: List<Line> }
                invariant List.length(items) <= 3
            """;

    private static final String BEHAVIOR = """

            behavior %1$s : (lines: List<Line>, rates: Map<Cur, Int>, k: Int, capped: Capped)
                    -> Bool
            let %1$s (lines, rates, k, capped) = %2$s
            """;

    private static final String PRICED = "Map.get(l.currency, rates)";

    /** Each count by name, and whether it is read, which is that no relation is left not shown
     *  to reach every value. */
    private static final Map<String, Boolean> CASES = cases();

    private static Map<String, Boolean> cases() {
        Map<String, Boolean> out = new LinkedHashMap<>();
        out.put("List.length(List.filter(l -> l.flag, lines)) == List.length(lines)", true);
        out.put("List.length(List.filter(l -> l.flag, lines)) <= List.length(lines)", true);
        out.put("List.length(List.filterMap(l -> " + PRICED + ", lines)) == List.length(lines)",
                true);
        out.put("List.length(List.filter(l -> Map.containsKey(l.currency, rates), lines))"
                + " == List.length(lines)", true);
        out.put("List.length(List.filter(l -> l.flag, lines)) == k", true);
        out.put("List.length(List.filterMap(l -> " + PRICED + ", lines)) == k", true);
        // No element meets the statement, so no row holds the count at anything but nought.
        out.put("List.length(List.filter(l -> l.flag && Bool.not(l.flag), lines)) == k", false);
        // A container the rules cap holds no more than three, and the count is no row past it.
        out.put("List.length(List.filter(l -> l.flag, capped.items)) == k", false);
        return out;
    }

    private static Map<String, PartitionEvidence> measured() {
        StringBuilder source = new StringBuilder(DECLARATIONS);
        int at = 0;
        for (Map.Entry<String, Boolean> each : CASES.entrySet()) {
            source.append(BEHAVIOR.formatted("case" + at++, each.getKey()));
        }
        Compilation compilation = Compilation.ofSource(source.toString(), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        return compilation.db().ask(new Adequacy.Coverage("probe")).value();
    }

    private static final Map<String, PartitionEvidence> MEASURED = measured();

    @Test
    void aCountIsShownToReachTheNumberItIsHeldAgainstWhereARowShowsEveryCount() {
        int at = 0;
        for (Map.Entry<String, Boolean> each : CASES.entrySet()) {
            PartitionEvidence evidence = MEASURED.get("case" + at++);
            assertNotNull(evidence, each.getKey());
            boolean refused = evidence.notRead().stream().anyMatch(left -> left.reason()
                    == UndividedPosition.Reason.RELATION_NOT_SHOWN_TO_REACH_EVERY_VALUE);
            assertEquals(!each.getValue(), refused, each.getKey());
        }
    }
}
