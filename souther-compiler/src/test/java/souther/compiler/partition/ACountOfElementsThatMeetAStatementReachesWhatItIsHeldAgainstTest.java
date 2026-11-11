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
 * that gets to the comparison. No row of the model is needed, since the rows are looked for among
 * the elements the statement itself tells apart: the values its type divides into, the values it
 * names, and each place it reads at once with the others.
 *
 * <p>A count so shown takes every value from none up to how many its container may hold, whatever
 * its container holds fewer of where a way to the comparison says so — a count of the elements of
 * a container of exactly two is none, one or two. Where no such row exists the count is not shown
 * to reach, and the relation stays unread there: a statement no element meets, and a container
 * whose rules cap how many it holds, which a count past it is no row of.
 *
 * <p>The numbers the statement reads are filed beside the count where there are any, and the
 * relation, whose count is at no place, shows nothing of them; what is asked here is the number
 * the count is held against.
 */
class ACountOfElementsThatMeetAStatementReachesWhatItIsHeldAgainstTest {

    private static final String DECLARATIONS = """
            module probe

            data Cur = String
                invariant String.matches("[A-Z]{3}", value)
            data Line = { currency: Cur, flag: Bool, a: Bool, b: Bool, qty: Int, amount: Decimal,
                          code: String }
            data Wide = { f1: Bool, f2: Bool, f3: Bool, f4: Bool, f5: Bool, f6: Bool, f7: Bool,
                          f8: Bool, f9: Bool }
            data Capped = { items: List<Line> }
                invariant List.length(items) <= 3
            data RateTable = Map<String, Int>
            data Items = List<String>
            data Pair = List<String>
                invariant List.length(value) >= 2
            data Ids = Set<Int>
            """;

    private static final String BEHAVIOR = """

            behavior %1$s : (lines: List<Line>, rates: Map<Cur, Int>, k: Int, capped: Capped,
                             flags: List<Bool>, names: List<String>, target: String,
                             wide: List<Wide>, table: RateTable, worn: Items, pair: Pair,
                             members: Set<Int>, wornSet: Ids, prices: Map<String, Int>) -> Bool
            let %1$s (lines, rates, k, capped, flags, names, target, wide, table, worn, pair,
                      members, wornSet, prices) = %2$s
            """;

    private static final String PRICED = "Map.get(l.currency, rates)";

    /** Nine places that must each be at the one value, which are more ways together than the
     *  figure the elements are tried to. */
    private static final String EVERY_FLAG_OFF = "List.length(List.filter(w -> "
            + "Bool.not(w.f1) && Bool.not(w.f2) && Bool.not(w.f3) && Bool.not(w.f4) && "
            + "Bool.not(w.f5) && Bool.not(w.f6) && Bool.not(w.f7) && Bool.not(w.f8) && "
            + "Bool.not(w.f9), wide)) == k";

    /** A count and the number it is held against, and whether that number is read. */
    private record Case(String body, String against, boolean read) {

        /** The count and the place that is asked about it: one count is asked of more than one. */
        String label() {
            return against + " of " + body;
        }
    }

    private static final List<Case> CASES = cases();

    private static List<Case> cases() {
        String size = "List.length(lines)";
        String flagged = "List.length(List.filter(l -> l.flag, lines))";
        String priced = "List.length(List.filterMap(l -> " + PRICED + ", lines))";
        return List.of(
                // Beside how many its container holds.
                new Case(flagged + " == " + size, size, true),
                new Case(flagged + " <= " + size, size, true),
                new Case(priced + " == " + size, size, true),
                new Case("List.length(List.filter(l -> Map.containsKey(l.currency, rates),"
                        + " lines)) == " + size, size, true),
                // Beside a number no place of the container ties.
                new Case(flagged + " == k", "k", true),
                new Case(priced + " == k", "k", true),
                // A statement over two places holds only where both are at the values it asks.
                new Case("List.length(List.filter(l -> Bool.not(l.a) && Bool.not(l.b), lines))"
                        + " == k", "k", true),
                // A statement that names a value tells the places it names apart there.
                new Case("List.length(List.filter(l -> l.qty > 5, lines)) == k", "k", true),
                new Case("List.length(List.filter(l -> l.qty > 5, lines)) == " + size, size,
                        true),
                new Case("List.length(List.filter(l -> l.code == \"USD\", lines)) == k", "k",
                        true),
                // The places the statement reads are the statement's own comparison's to divide,
                // and the count leaves none of them unread.
                new Case("List.length(List.filter(l -> l.qty > 5, lines)) == k", "lines[*].qty",
                        true),
                new Case("List.length(List.filter(l -> l.code == \"USD\", lines)) == k",
                        "lines[*].code", true),
                // The value a number is named at is written as the type of the place writes it.
                new Case("List.length(List.filter(l -> l.amount > 5.0m, lines)) == k", "k", true),
                // A statement about the element itself and not a field of it.
                new Case("List.length(List.filter(x -> x, flags)) == k", "k", true),
                new Case("List.length(List.filter(n -> n == target, names)) == k", "k", true),
                // A collection a newtype wraps is held as that newtype where a statement reads it.
                new Case("List.length(List.filter(x -> Map.containsKey(x, table.value), names))"
                        + " == k", "k", true),
                // The container counted is the parameter it is: held as the newtype that wraps it,
                // and with as many elements as a rule on it asks for.
                new Case("List.length(List.filter(x -> x == \"USD\", worn.value)) == k", "k",
                        true),
                new Case("List.length(List.filter(x -> x == \"USD\", pair.value)) == k", "k",
                        true),
                // A set holds each element once, and what one element meets and another fails are
                // two values already; a map's entries are a key and a value, built apart.
                new Case("Set.size(Set.filter(x -> x > 5, members)) == k", "k", true),
                new Case("Set.size(Set.filter(x -> x > 5, wornSet.value)) == k", "k", true),
                new Case("Map.size(Map.filterEntries((key, v) -> v > 5, prices)) == k", "k",
                        false),
                // What a way says of the size of the container is no more than the most the count
                // is, and the count is none up to that.
                new Case("if List.length(lines) == 2 then " + flagged + " == k else false", "k",
                        true),
                new Case("if List.length(lines) >= 2 then " + flagged + " == k else false", "k",
                        true),
                new Case("if List.length(lines) <= 3 then " + flagged + " == k else false", "k",
                        true),
                // A measure of a place is no value of it: what the statement names of one is a
                // value that holds that many, which the type of the place builds.
                new Case("List.length(List.filter(l -> String.length(l.code) > 3, lines)) == k",
                        "k", true),
                // No element meets the statement, so no row holds the count at anything but none.
                new Case("List.length(List.filter(l -> l.flag && Bool.not(l.flag), lines)) == k",
                        "k", false),
                // More ways to be together than the figure: the ones past it are not tried, and the
                // figure is what is said.
                new Case(EVERY_FLAG_OFF, "k", false),
                // A container the rules cap holds no more than three, and a count past it is no
                // row of.
                new Case("List.length(List.filter(l -> l.flag, capped.items)) == k", "k", false));
    }

    private static Map<String, PartitionEvidence> measured() {
        StringBuilder source = new StringBuilder(DECLARATIONS);
        int at = 0;
        for (Case each : CASES) {
            source.append(BEHAVIOR.formatted("case" + at++, each.body()));
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
        Map<String, Boolean> refused = new LinkedHashMap<>();
        int at = 0;
        for (Case each : CASES) {
            PartitionEvidence evidence = MEASURED.get("case" + at++);
            assertNotNull(evidence, each.body());
            refused.put(each.label(), evidence.notRead().stream().anyMatch(left ->
                    left.at().equals(each.against())
                            && left.reason() == UndividedPosition.Reason
                                    .RELATION_NOT_SHOWN_TO_REACH_EVERY_VALUE));
        }
        Map<String, Boolean> expected = new LinkedHashMap<>();
        CASES.forEach(each -> expected.put(each.label(), !each.read()));
        assertEquals(expected, refused);
    }

    /**
     * What was not tried is said, and not only that nothing was shown: a search that stopped short
     * of everything it would have tried names the figure it stopped at, whether or not the ways it
     * left are ones the rules would have refused.
     */
    @Test
    void aSearchCutShortSaysTheFigureItStoppedAt() {
        int at = CASES.indexOf(CASES.stream().filter(each -> each.body().equals(EVERY_FLAG_OFF))
                .findFirst().orElseThrow());
        assertEquals(List.of(souther.compiler.partition.CompositionBudget
                        .VALUES_AN_ELEMENT_IS_CHOSEN_AMONG.figure()),
                MEASURED.get("case" + at).notRead().stream()
                        .filter(left -> left.at().equals("k"))
                        .flatMap(left -> left.figures().stream()).distinct().toList());
    }
}
