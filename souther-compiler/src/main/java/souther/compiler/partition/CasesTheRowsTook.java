package souther.compiler.partition;

import souther.compiler.inputs.Quantities;
import souther.compiler.meaning.Proposition;

import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
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
 * <p><b>A row is evidence of a case only where its run went through the statement that draws
 * it.</b> That is the rule the row was placed at consulting the statement ({@link RulesTaken}):
 * every condition of a rule was seen coming out as the rule says, so a statement it consults is one
 * the run reached. What the row writes is only what tells the case apart, never that the run met
 * it — a row that switches the statement off and holds a key twice is an input the statement would
 * tell apart and was not asked.
 *
 * <p>The cases of a search are the steps of the recursion and not depths: the node it starts at
 * meets what it asks; that node does not and the search finds one below; that node does not and has
 * nothing below, where the recursion stops empty; or that node does not and every child searched
 * came back empty, where it continues and comes back empty. A row is in the first two where the
 * search came out finding one and in the last two where it did not, and which of the two is what
 * the statement asks of the node it starts at — whether it meets it, or has nothing below —
 * answered at the row.
 *
 * <p>The cases of a key held twice are of one order at a time. A statement resting on two maps,
 * each filed from a list of its own, rests on two orders, and what one decides is not what the
 * other does: each is read the other way round with the rest left as they are, and two orders read
 * together can undo each other. For one order the two ways round it decides are a row the statement
 * holds of with the last element the entry and fails of with the first, and a row the other way.
 *
 * <p>A case is owed only where the decision says the statement can come out its way: a search no
 * rule has come out finding one owes no case of finding one. A statement this reading cannot ask of
 * a row owes every case it draws and is seen in none.
 */
public final class CasesTheRowsTook {

    /** A kind of case some statement of the decision draws inside itself. */
    public enum Kind {
        /** The step of the recursion a search from a node took: where it found what it asks, and
         *  where it came back empty. */
        A_NODE_A_SEARCH_REACHES,
        /** Which element of a key held twice a map filed from a list holds. */
        THE_ORDER_OF_A_REPEATED_KEY
    }

    /**
     * The cases of a search from a node, which are the steps of the recursion it is and not depths:
     * the node meets what it asks, and the search stops there; the node does not and the search
     * goes on to its children and finds one below; the node does not and has nothing below, which
     * is where the recursion stops empty; or the node does not and every child searched came back
     * empty, which is the recursion continuing and coming back empty.
     */
    private enum OfASearch { AT_THE_NODE, BELOW_IT, NOWHERE_AT_A_LEAF, NOWHERE_BELOW }

    /** The two ways round the order of a repeated key decides a statement. */
    private enum OfAnOrder { HOLDS_BY_THE_LAST, FAILS_BY_THE_LAST }

    /** One order a statement rests on, which is the distinction a row is read the other way in. */
    private record Order(Proposition statement, StandingAtAPoint.OrderOfAKey of) {}

    private final DecisionReading read;
    private final BehaviorInputs inputs;
    private final Quantities quantities;
    private final Map<Proposition.SomeReachable, Set<OfASearch>> searchesOwe = new LinkedHashMap<>();
    private final Map<Proposition.SomeReachable, Set<OfASearch>> searchesSeen =
            new LinkedHashMap<>();
    private final Set<Order> ordersOwe = new LinkedHashSet<>();
    private final Map<Order, Set<OfAnOrder>> ordersSeen = new LinkedHashMap<>();
    /** The kinds some statement draws a case of that no row can be asked about. */
    private final Set<Kind> unaskable = EnumSet.noneOf(Kind.class);

    /** Owed nothing, so nothing of the reading is ever asked. */
    private CasesTheRowsTook() {
        this.read = null;
        this.inputs = null;
        this.quantities = null;
    }

    private CasesTheRowsTook(DecisionReading read, BehaviorInputs inputs, Quantities quantities) {
        this.read = read;
        this.inputs = inputs;
        this.quantities = quantities;
        for (DecisionReading.Ruled each : read.found()) {
            each.rule().consulted().forEach((condition, decided) -> {
                if (!(condition instanceof DecisionCondition.AStatement(Proposition stated))
                        || !(decided instanceof DecidedCondition.Held(var _, boolean held))) {
                    return;
                }
                if (Proposition.saysASearchReachesBelow(stated)) {
                    if (stated instanceof Proposition.SomeReachable search) {
                        Set<OfASearch> owed = owedBy(search, held == search.holds());
                        if (owed.isEmpty()) {
                            unaskable.add(Kind.A_NODE_A_SEARCH_REACHES);
                        } else {
                            searchesOwe.computeIfAbsent(search,
                                    _ -> EnumSet.noneOf(OfASearch.class)).addAll(owed);
                        }
                    } else {
                        unaskable.add(Kind.A_NODE_A_SEARCH_REACHES);
                    }
                }
                for (Proposition.LastToHold last : stated.lastsToHold()) {
                    StandingAtAPoint.OrderOfAKey order = StandingAtAPoint.OrderOfAKey.of(last);
                    if (order == null) {
                        unaskable.add(Kind.THE_ORDER_OF_A_REPEATED_KEY);
                    } else {
                        ordersOwe.add(new Order(stated, order));
                    }
                }
            });
        }
    }

    /**
     * What the cases {@code read} draws inside its statements are owed, to be taken in by the rows
     * placed at its rules ({@link #see}) and asked what none was seen in ({@link #unseen}).
     *
     * @param inputs     what the behavior takes, as its rows are walked
     * @param quantities the numbers of the input the statements are about
     */
    public static CasesTheRowsTook of(DecisionReading read, BehaviorInputs inputs,
                                      Quantities quantities) {
        return new CasesTheRowsTook(read, inputs, quantities);
    }

    /** The cases of a decision no one reads, which are owed none and are seen in none. */
    public static CasesTheRowsTook none() {
        return new CasesTheRowsTook();
    }

    /**
     * Whether a row can be asked which step of the recursion {@code search} took: where the node it
     * starts at is the one its statement is written of, and the statement says what it is for that
     * node to have nothing below. Anywhere else a search that came out empty went through a step
     * no row can be told from the other.
     */
    private static boolean tellsTheStepsApart(Proposition.SomeReachable search) {
        return search.at().equals(search.writtenAt()) && search.noneBelow().isPresent();
    }

    /**
     * The cases of {@code search} owed where it comes out finding a node, or not; none where a
     * case it comes out in cannot be told from another, and then it is owed one nothing is seen
     * in.
     */
    private static Set<OfASearch> owedBy(Proposition.SomeReachable search, boolean finds) {
        if (!finds) {
            return tellsTheStepsApart(search)
                    ? EnumSet.of(OfASearch.NOWHERE_AT_A_LEAF, OfASearch.NOWHERE_BELOW)
                    : EnumSet.noneOf(OfASearch.class);
        }
        // A search starting below where its statement is written reaches no node that statement is
        // asked of first, so finding one is finding one below.
        return search.at().equals(search.writtenAt())
                ? EnumSet.of(OfASearch.AT_THE_NODE, OfASearch.BELOW_IT)
                : EnumSet.of(OfASearch.BELOW_IT);
    }

    /**
     * Takes in what {@code row} is evidence of: the cases of the statements the rule it was placed
     * at consulted. A row placed at no rule went through none this can tell, and is evidence of no
     * case — so a caller hands over the rows it placed and none it did not.
     */
    public void see(ObservedInputs row, DecisionRule rule) {
        if (searchesOwe.isEmpty() && ordersOwe.isEmpty()) {
            return;
        }
        rule.consulted().forEach((condition, decided) -> {
            if (!(condition instanceof DecisionCondition.AStatement(Proposition stated))
                    || !(decided instanceof DecidedCondition.Held(var _, boolean held))) {
                return;
            }
            if (stated instanceof Proposition.SomeReachable search) {
                OfASearch seen = caseOf(search, held == search.holds(), row);
                if (seen != null) {
                    searchesSeen.computeIfAbsent(search, _ -> EnumSet.noneOf(OfASearch.class))
                            .add(seen);
                }
            }
            seeOrders(stated, row);
        });
    }

    /**
     * The orders {@code stated} rests on that the row tells apart: read the other way round, with
     * every other order as it is, the statement comes out the other way.
     */
    private void seeOrders(Proposition stated, ObservedInputs row) {
        Set<StandingAtAPoint.OrderOfAKey> orders = new LinkedHashSet<>();
        for (Proposition.LastToHold last : stated.lastsToHold()) {
            StandingAtAPoint.OrderOfAKey order = StandingAtAPoint.OrderOfAKey.of(last);
            if (order != null) {
                orders.add(order);
            }
        }
        if (orders.isEmpty()) {
            return;
        }
        StandingAtAPoint.AtTheRow asItIs = StandingAtAPoint.atTheRow(stated, read.behavior(),
                quantities, inputs, row, Set.of());
        for (StandingAtAPoint.OrderOfAKey order : orders) {
            StandingAtAPoint.AtTheRow otherWay = StandingAtAPoint.atTheRow(stated, read.behavior(),
                    quantities, inputs, row, Set.of(order));
            OfAnOrder seen = asItIs == StandingAtAPoint.AtTheRow.HOLDS
                    && otherWay == StandingAtAPoint.AtTheRow.FAILS ? OfAnOrder.HOLDS_BY_THE_LAST
                    : asItIs == StandingAtAPoint.AtTheRow.FAILS
                    && otherWay == StandingAtAPoint.AtTheRow.HOLDS ? OfAnOrder.FAILS_BY_THE_LAST
                    : null;
            if (seen != null) {
                ordersSeen.computeIfAbsent(new Order(stated, order),
                        _ -> EnumSet.noneOf(OfAnOrder.class)).add(seen);
            }
        }
    }

    /**
     * The case of {@code search} a row it came out {@code found} at was in, or null where what it
     * asks of the node it starts at could not be read off the row.
     */
    private OfASearch caseOf(Proposition.SomeReachable search, boolean found, ObservedInputs row) {
        if (!found) {
            // Empty at a leaf where the node has nothing below it, and through its children where
            // it has some and none of them found one.
            return !tellsTheStepsApart(search) ? null : switch (StandingAtAPoint.atTheRow(
                    search.noneBelow().orElseThrow(), read.behavior(), quantities, inputs, row,
                    Set.of())) {
                case HOLDS -> OfASearch.NOWHERE_AT_A_LEAF;
                case FAILS -> OfASearch.NOWHERE_BELOW;
                case COULD_NOT_TELL -> null;
            };
        }
        if (!search.at().equals(search.writtenAt())) {
            return OfASearch.BELOW_IT;
        }
        return switch (StandingAtAPoint.atTheRow(search.atANode(), read.behavior(), quantities,
                inputs, row, Set.of())) {
            case HOLDS -> OfASearch.AT_THE_NODE;
            case FAILS -> OfASearch.BELOW_IT;
            case COULD_NOT_TELL -> null;
        };
    }

    /** The kinds of case some statement draws that none of the rows seen was in. */
    public Set<Kind> unseen() {
        Set<Kind> out = EnumSet.noneOf(Kind.class);
        out.addAll(unaskable);
        searchesOwe.forEach((search, owed) -> {
            if (!searchesSeen.getOrDefault(search, Set.of()).containsAll(owed)) {
                out.add(Kind.A_NODE_A_SEARCH_REACHES);
            }
        });
        for (Order order : ordersOwe) {
            if (ordersSeen.getOrDefault(order, Set.of()).size() < OfAnOrder.values().length) {
                out.add(Kind.THE_ORDER_OF_A_REPEATED_KEY);
            }
        }
        return out;
    }
}
