package souther.bench.readings.orders;

import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

/**
 * Readers that take the order of a copy into an answer, one way apiece.
 *
 * <p>Every public method here is one the walk must refuse, and the test that reads this class takes
 * them off the class rather than from a list: a way of taking an order added here is a way the walk
 * is asked about without anyone saying so. What each does is the whole of its name — a list made of
 * the copy, a text that says it, the first one a stream reaches, one at an index.
 *
 * <p>Some do not list anything. Where many elements meet in one place the walk's order says which is
 * left: the element a single step reaches, the value a shared key is left holding, what a sort
 * leaves first among the things it ties.
 */
public final class WalkedIntoAnAnswer {

    private WalkedIntoAnAnswer() {}

    public static List<CompositionBudget> copiedIntoAList(Held held) {
        return List.copyOf(held.figures());
    }

    public static List<CompositionBudget> gatheredOneAtATime(Held held) {
        List<CompositionBudget> out = new ArrayList<>();
        for (CompositionBudget each : held.figures()) {
            out.add(each);
        }
        return out;
    }

    public static CompositionBudget theFirstOneThatMatches(Held held) {
        return held.figures().stream().filter(each -> each.ordinal() > 0).findFirst()
                .orElseThrow();
    }

    public static String joinedIntoATextByACollector(Held held) {
        return held.figures().stream().map(Enum::name).collect(Collectors.joining(","));
    }

    public static String joinedIntoATextByAConcatenation(Held held) {
        return "figures: " + held.figures();
    }

    public static String joinedIntoATextByAnAppend(Held held) {
        StringBuilder out = new StringBuilder();
        out.append(held.figures());
        return out.toString();
    }

    public static List<CompositionBudget> theValuesOfAMapAsAList(Held held) {
        return held.named().values().stream().toList();
    }

    public static CompositionBudget theOneAtAnIndexOfACopyOfTheValues(Held held) {
        return new ArrayList<>(held.named().values()).get(0);
    }

    public static Object[] anArray(Held held) {
        return held.figures().toArray();
    }

    public static List<CompositionBudget> handedToAHelperThatMakesAList(Held held) {
        return listed(held.figures());
    }

    private static List<CompositionBudget> listed(Collection<CompositionBudget> these) {
        return new ArrayList<>(these);
    }

    public static List<String> filledByAFunctionOfAWalk(Held held) {
        List<String> out = new ArrayList<>();
        held.figures().forEach(each -> out.add(each.name()));
        return out;
    }

    public static List<CompositionBudget> filledByAHelperThatAddsToItsArgument(Held held) {
        List<CompositionBudget> out = new ArrayList<>();
        addEach(out, held.figures());
        return out;
    }

    private static void addEach(List<CompositionBudget> into,
                                Collection<CompositionBudget> these) {
        for (CompositionBudget each : these) {
            into.add(each);
        }
    }

    public static List<String> theKeysOfAMapAsAList(Held held) {
        return new ArrayList<>(held.named().keySet());
    }

    public static Map<String, CompositionBudget> aMapThatKeepsTheOrderItWasFilledIn(Held held) {
        return new LinkedHashMap<>(held.named());
    }

    public static Set<CompositionBudget> aSetThatKeepsTheOrderItWasFilledIn(Held held) {
        return new LinkedHashSet<>(held.figures());
    }

    public static List<String> namedByAStreamAndKeptAsAList(Held held) {
        return held.figures().stream().map(Enum::name).toList();
    }

    public static List<CompositionBudget> namedByAnImpostor(Held held) {
        return Impostor.keep(held.figures());
    }

    public static CompositionBudget theFirstOneASingleStepReaches(Held held) {
        return held.figures().iterator().next();
    }

    public static Map<String, CompositionBudget> theLastOneLeftUnderAKeyTheyShare(Held held) {
        Map<String, CompositionBudget> out = new HashMap<>();
        held.figures().forEach(each -> out.put("same", each));
        return out;
    }

    public static Map<String, CompositionBudget> theFirstOneLeftUnderAKeyTheyShare(Held held) {
        Map<String, CompositionBudget> out = new HashMap<>();
        for (CompositionBudget each : held.figures()) {
            out.putIfAbsent("same", each);
        }
        return out;
    }

    public static Map<String, CompositionBudget> mergedByAFunctionThatKeepsTheNewer(Held held) {
        Map<String, CompositionBudget> out = new HashMap<>();
        held.figures().forEach(each -> out.merge("same", each, (older, newer) -> newer));
        return out;
    }

    public static Map<String, CompositionBudget> collectedByAMergeThatKeepsTheNewer(Held held) {
        return held.figures().stream().collect(
                Collectors.toMap(each -> "same", each -> each, (older, newer) -> newer));
    }

    public static Map<Integer, List<CompositionBudget>> groupedIntoListsByACollector(Held held) {
        return held.figures().stream().collect(Collectors.groupingBy(each -> each.ordinal() % 2));
    }

    public static Map<Integer, List<CompositionBudget>> groupedIntoListsByHand(Held held) {
        Map<Integer, List<CompositionBudget>> out = new HashMap<>();
        for (CompositionBudget each : held.figures()) {
            out.computeIfAbsent(each.ordinal() % 2, _ -> new ArrayList<>()).add(each);
        }
        return out;
    }

    public static List<CompositionBudget> sortedByAKeyTwoOfThemCanShare(Held held) {
        return held.figures().stream()
                .sorted(Comparator.comparingInt(each -> each.ordinal() / 2)).toList();
    }

    public static List<CompositionBudget> sortedInPlaceByAKeyTwoOfThemCanShare(Held held) {
        List<CompositionBudget> out = new ArrayList<>(held.figures());
        out.sort(Comparator.comparingInt(each -> each.ordinal() / 2));
        return out;
    }

    public static List<CompositionBudget> keptByATreeThatTiesTwoOfThem(Held held) {
        Set<CompositionBudget> tree =
                new TreeSet<>(Comparator.comparingInt(each -> each.ordinal() / 2));
        tree.addAll(held.figures());
        return new ArrayList<>(tree);
    }
}
