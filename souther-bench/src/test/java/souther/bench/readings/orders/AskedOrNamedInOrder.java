package souther.bench.readings.orders;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.NumericTerms;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.publish.PublicationOrders;
import souther.compiler.query.WeakeningSet;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.stream.Collectors;

/**
 * Readers that walk a copy and put nothing of its order in an answer.
 *
 * <p>Every public method here is one the walk must pass, each a different way of not doing so: the
 * copy is handed to what puts it in an order, asked what it holds, folded by something that does
 * not care which comes first, or filled into something without an order. Iterating a copy is not
 * what the walk refuses, and the ones that iterate here are there to say so.
 */
public final class AskedOrNamedInOrder {

    private AskedOrNamedInOrder() {}

    public static List<CompositionBudget> putInThePublishedOrder(Held held) {
        return PublicationOrders.COMPOSITION_BUDGETS.keep(held.figures()).written();
    }

    public static List<NumericTerm> putInTheTermsOwnOrder(Held held) {
        return NumericTerms.inOrder(held.terms());
    }

    public static WeakeningSet foldedByAnOperationThatDoesNotCareWhichComesFirst(Held held) {
        return WeakeningSet.ofAll(held.weakenings());
    }

    public static boolean askedWhatItHolds(Held held, CompositionBudget one) {
        return held.figures().contains(one) && !held.figures().isEmpty()
                && held.figures().size() > 1 && held.named().containsKey("a")
                && held.named().get("b") == one;
    }

    public static int summedOverAWalk(Held held) {
        int total = 0;
        for (CompositionBudget each : held.figures()) {
            total += each.ordinal();
        }
        return total;
    }

    public static boolean askedOfEveryOne(Held held) {
        return held.figures().stream().anyMatch(each -> each.ordinal() > 1);
    }

    public static Set<String> filledIntoASetOfNames(Held held) {
        return held.figures().stream().map(Enum::name).collect(Collectors.toSet());
    }

    public static Map<String, Integer> countedByAFunctionOfAWalk(Held held) {
        Map<String, Integer> out = new HashMap<>();
        held.figures().forEach(each -> out.merge(each.name(), 1, Integer::sum));
        return out;
    }

    public static Set<CompositionBudget> putTogetherInASetThatPutsThemInTheirOwnOrder(
            Held one, Held other) {
        Set<CompositionBudget> both = EnumSet.noneOf(CompositionBudget.class);
        both.addAll(one.figures());
        both.addAll(other.figures());
        return both;
    }

    public static Map<String, CompositionBudget> aMapThatKeepsItsKeysInTheirOwnOrder(Held held) {
        return new TreeMap<>(held.named());
    }

    public static List<String> sortedByAKeyBeforeItIsKeptAsAList(Held held) {
        return held.figures().stream().map(Enum::name).sorted().toList();
    }

    public static List<CompositionBudget> madeAListAndThenSortedIt(Held held) {
        List<CompositionBudget> out = new ArrayList<>(held.figures());
        out.sort(Comparator.comparing(Enum::name));
        return out;
    }

    public static List<CompositionBudget> handedToAHelperThatPutsThemInOrder(Held held) {
        return inOrder(held.figures());
    }

    private static List<CompositionBudget> inOrder(Collection<CompositionBudget> these) {
        return PublicationOrders.COMPOSITION_BUDGETS.keep(these).written();
    }

    public static void saidInTheMessageOfAnExceptionOnly(Held held) {
        if (held.figures().isEmpty()) {
            throw new IllegalStateException("no figure among " + held.figures());
        }
    }
}
