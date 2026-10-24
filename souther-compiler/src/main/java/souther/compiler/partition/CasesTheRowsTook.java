package souther.compiler.partition;

import souther.compiler.inputs.Quantities;
import souther.compiler.meaning.Proposition;

import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Which of the cases a statement of a decision tells apart inside itself the rows were seen in, and
 * so which kinds of case no row has stood in yet.
 *
 * <p>A rule is told apart by how each of its conditions came out, and a condition is a whole
 * statement. Two statements draw distinctions a rule does not: a search from a node, which comes out
 * one way at the node it starts at and the same way at a node further down; and a statement about
 * the entry a map filed from a list holds under a key, which is the last element of the key and not
 * an earlier one. Rows taking every rule may still all be rows of one side of such a distinction,
 * so the cases are asked of the rows themselves.
 *
 * <p>The cases of a search are the inductive ones and not depths: the node it starts at meets what
 * it asks; that node does not and the search still finds one below; or it finds none. A row is in
 * the first two where the search came out finding one, and which of them is what the statement
 * asks of the node it starts at, read off the row.
 *
 * <p>The cases of a key held twice are the two ways round its order decides: a row the statement
 * holds of with the last element the entry and fails of with the first, and a row the other way.
 * Either is a row where which element of a key comes last is what the answer turned on.
 *
 * <p>A case is owed only where the decision says the statement can come out its way: a search no
 * rule has come out finding one owes no case of finding one. A statement this reading cannot ask of
 * a row owes every case it draws and is seen in none.
 */
public final class CasesTheRowsTook {

    /** A kind of case some statement of the decision draws inside itself. */
    public enum Kind {
        /** Where a search from a node finds what it asks: at the node, below it, or nowhere. */
        A_NODE_A_SEARCH_REACHES,
        /** Which element of a key held twice a map filed from a list holds. */
        THE_ORDER_OF_A_REPEATED_KEY
    }

    /** The cases of a search from a node. */
    private enum OfASearch { AT_THE_NODE, BELOW_IT, NOWHERE }

    /** The two ways round the order of a repeated key decides a statement. */
    private enum OfAnOrder { HOLDS_BY_THE_LAST, FAILS_BY_THE_LAST }

    private final DecisionReading read;
    private final Map<Proposition.SomeReachable, Set<OfASearch>> searchesOwe = new LinkedHashMap<>();
    private final Map<Proposition.SomeReachable, Set<OfASearch>> searchesSeen =
            new LinkedHashMap<>();
    private final Set<Proposition> ordersOwe = new LinkedHashSet<>();
    private final Map<Proposition, Set<OfAnOrder>> ordersSeen = new LinkedHashMap<>();
    /** Whether some statement draws a case of this kind that no row can be asked about. */
    private final Set<Kind> unaskable = EnumSet.noneOf(Kind.class);

    private CasesTheRowsTook(DecisionReading read) {
        this.read = read;
        for (DecisionReading.Ruled each : read.found()) {
            each.rule().consulted().forEach((condition, decided) -> {
                if (!(condition instanceof DecisionCondition.AStatement(Proposition stated))
                        || !(decided instanceof DecidedCondition.Held(var _, boolean held))) {
                    return;
                }
                if (Proposition.saysASearchReachesBelow(stated)) {
                    if (stated instanceof Proposition.SomeReachable search) {
                        searchesOwe.computeIfAbsent(search, _ -> EnumSet.noneOf(OfASearch.class))
                                .addAll(owedBy(search, held == search.holds()));
                    } else {
                        unaskable.add(Kind.A_NODE_A_SEARCH_REACHES);
                    }
                }
                if (Proposition.saysTheLastToHold(stated)) {
                    ordersOwe.add(stated);
                }
            });
        }
    }

    /**
     * Which cases {@code read} draws inside its statements that none of {@code rows} was seen in,
     * by kind.
     *
     * @param rows each row as it ran, with the rule it was placed at where it was placed
     */
    public static Set<Kind> unseen(DecisionReading read, RunPlacement placement,
                                   Quantities quantities, List<ObservedInputs> rows) {
        CasesTheRowsTook cases = new CasesTheRowsTook(read);
        if (cases.searchesOwe.isEmpty() && cases.ordersOwe.isEmpty()) {
            return cases.unaskable;
        }
        for (ObservedInputs row : rows) {
            if (row.watched() instanceof Generator.Watched.Ran) {
                cases.see(row, placement, quantities);
            }
        }
        return cases.unseen();
    }

    /** The cases of {@code search} owed where it comes out finding a node, or not. */
    private static Set<OfASearch> owedBy(Proposition.SomeReachable search, boolean finds) {
        if (!finds) {
            return EnumSet.of(OfASearch.NOWHERE);
        }
        // A search starting below where its statement is written reaches no node that statement is
        // asked of first, so finding one is finding one below.
        return search.at().equals(search.writtenAt())
                ? EnumSet.of(OfASearch.AT_THE_NODE, OfASearch.BELOW_IT)
                : EnumSet.of(OfASearch.BELOW_IT);
    }

    private void see(ObservedInputs row, RunPlacement placement, Quantities quantities) {
        if (!searchesOwe.isEmpty()
                && placement.takenBy(row) instanceof RulesTaken.WhichRule.TookThis took) {
            took.rule().consulted().forEach((condition, decided) -> {
                if (condition instanceof DecisionCondition.AStatement(Proposition stated)
                        && stated instanceof Proposition.SomeReachable search
                        && decided instanceof DecidedCondition.Held(var _, boolean held)) {
                    OfASearch seen = caseOf(search, held == search.holds(), row, placement,
                            quantities);
                    if (seen != null) {
                        searchesSeen.computeIfAbsent(search,
                                _ -> EnumSet.noneOf(OfASearch.class)).add(seen);
                    }
                }
            });
        }
        for (Proposition stated : ordersOwe) {
            StandingAtAPoint.AtTheRow byTheLast = StandingAtAPoint.atTheRow(stated,
                    read.behavior(), quantities, placement.inputs(), row, false);
            StandingAtAPoint.AtTheRow byTheFirst = StandingAtAPoint.atTheRow(stated,
                    read.behavior(), quantities, placement.inputs(), row, true);
            OfAnOrder seen = byTheLast == StandingAtAPoint.AtTheRow.HOLDS
                    && byTheFirst == StandingAtAPoint.AtTheRow.FAILS ? OfAnOrder.HOLDS_BY_THE_LAST
                    : byTheLast == StandingAtAPoint.AtTheRow.FAILS
                    && byTheFirst == StandingAtAPoint.AtTheRow.HOLDS ? OfAnOrder.FAILS_BY_THE_LAST
                    : null;
            if (seen != null) {
                ordersSeen.computeIfAbsent(stated, _ -> EnumSet.noneOf(OfAnOrder.class)).add(seen);
            }
        }
    }

    /**
     * The case of {@code search} a row it came out {@code found} at was in, or null where what it
     * asks of the node it starts at could not be read off the row.
     */
    private OfASearch caseOf(Proposition.SomeReachable search, boolean found, ObservedInputs row,
                             RunPlacement placement, Quantities quantities) {
        if (!found) {
            return OfASearch.NOWHERE;
        }
        if (!search.at().equals(search.writtenAt())) {
            return OfASearch.BELOW_IT;
        }
        return switch (StandingAtAPoint.atTheRow(search.atANode(), read.behavior(), quantities,
                placement.inputs(), row, false)) {
            case HOLDS -> OfASearch.AT_THE_NODE;
            case FAILS -> OfASearch.BELOW_IT;
            case COULD_NOT_TELL -> null;
        };
    }

    private Set<Kind> unseen() {
        Set<Kind> out = EnumSet.noneOf(Kind.class);
        out.addAll(unaskable);
        searchesOwe.forEach((search, owed) -> {
            if (!searchesSeen.getOrDefault(search, Set.of()).containsAll(owed)) {
                out.add(Kind.A_NODE_A_SEARCH_REACHES);
            }
        });
        for (Proposition stated : ordersOwe) {
            if (ordersSeen.getOrDefault(stated, Set.of()).size() < OfAnOrder.values().length) {
                out.add(Kind.THE_ORDER_OF_A_REPEATED_KEY);
            }
        }
        return out;
    }
}
