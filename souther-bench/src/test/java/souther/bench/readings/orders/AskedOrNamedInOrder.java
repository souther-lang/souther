package souther.bench.readings.orders;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.NumericTerms;
import souther.compiler.partition.ClassOfAPosition;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.publish.PublicationOrders;
import souther.compiler.query.WeakeningSet;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
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
            total += each.name().length();
        }
        return total;
    }

    public static boolean askedOfEveryOne(Held held) {
        return held.figures().stream().anyMatch(each -> each.name().length() > 1);
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

    public static Map<ClassOfAPosition, String> aMapThatKeepsItsKeysInADeclaredOrder(
            HeldClasses held) {
        Map<ClassOfAPosition, String> out = new TreeMap<>(ClassOfAPosition.steadyOrder());
        out.putAll(held.named());
        return out;
    }

    public static List<ClassOfAPosition> sortedByADeclaredOrder(HeldClasses held) {
        return held.classes().stream().sorted(ClassOfAPosition.steadyOrder()).toList();
    }

    public static List<ClassOfAPosition> madeAListAndThenSortedItByADeclaredOrder(
            HeldClasses held) {
        List<ClassOfAPosition> out = new ArrayList<>(held.classes());
        out.sort(ClassOfAPosition.steadyOrder());
        return out;
    }

    public static List<ClassOfAPosition> sortedByAKeyAndThenByADeclaredOrder(HeldClasses held) {
        return held.classes().stream()
                .sorted(Comparator.comparing((ClassOfAPosition each) -> each.classId())
                        .thenComparing(ClassOfAPosition.steadyOrder()))
                .toList();
    }

    public static CompositionBudget theOnlyOneOfASetThatHoldsOne(Held held) {
        if (held.figures().size() != 1) {
            throw new IllegalStateException("not one figure but " + held.figures().size());
        }
        return held.figures().iterator().next();
    }

    public static Map<CompositionBudget, String> keyedByTheElementItself(Held held) {
        Map<CompositionBudget, String> out = new HashMap<>();
        for (CompositionBudget each : held.figures()) {
            out.put(each, each.name());
        }
        return out;
    }

    public static Map<String, CompositionBudget> keyedByTheKeyOfTheEntryItCameFrom(Held held) {
        Map<String, CompositionBudget> out = new HashMap<>();
        for (Map.Entry<String, CompositionBudget> each : held.named().entrySet()) {
            out.put(each.getKey(), each.getValue());
        }
        return out;
    }

    public static Map<String, CompositionBudget> collectedByAKeyThatTwoOfThemCannotShare(
            Held held) {
        return held.figures().stream().collect(Collectors.toMap(Enum::name, each -> each));
    }

    public static Set<CompositionBudget> retainedByWhatTheCopyHolds(Held held,
                                                                    Set<CompositionBudget> other) {
        Set<CompositionBudget> out = new HashSet<>(other);
        out.retainAll(held.figures());
        return out;
    }

    public static List<CompositionBudget> clearedAfterTheWalk(Held held) {
        List<CompositionBudget> out = new ArrayList<>(held.figures());
        out.clear();
        return out;
    }

    public static Set<String> theTextOfEachElementStripped(Held held) {
        Set<String> out = new HashSet<>();
        for (CompositionBudget each : held.figures()) {
            out.add(each.name().stripTrailing());
        }
        return out;
    }

    public static Set<BigDecimal> decimalsMadeOfTheNameOfEachElement(Held held) {
        Set<BigDecimal> out = new HashSet<>();
        for (CompositionBudget each : held.figures()) {
            out.add(new BigDecimal(each.name().length()));
        }
        return out;
    }

    public static int whereAColonStandsInTheNameOfEachElement(Held held) {
        int total = 0;
        for (CompositionBudget each : held.figures()) {
            total += each.name().indexOf('_');
        }
        return total;
    }

    public static void printedHowManyThereAre(Held held) {
        System.out.println(held.figures().size());
    }

    public static boolean askedWhetherTheyShareOneWithAnother(Held held,
                                                              Set<CompositionBudget> other) {
        return Collections.disjoint(held.figures(), other);
    }

    public static ClassOfAPosition theLeastByADeclaredOrder(HeldClasses held) {
        return held.classes().stream().min(ClassOfAPosition.steadyOrder()).orElseThrow();
    }

    public static Map<Integer, Long> countedInGroups(Held held) {
        return held.figures().stream().collect(
                Collectors.groupingBy(each -> each.name().length() % 2, Collectors.counting()));
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
