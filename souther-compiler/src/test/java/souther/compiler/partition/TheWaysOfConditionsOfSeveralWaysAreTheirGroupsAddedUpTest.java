package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.partition.OneOfEach.Step;
import souther.compiler.partition.OneOfEach.Walked;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The ways conditions of several ways come to: every way a row takes where the figure lets them
 * all be handed on, and otherwise some of them with the figure that left the rest — with the
 * looking for them the ways of each group that turns on positions in common, added up and not
 * multiplied, and a proof that nothing is past them only from a group walked to its end.
 */
class TheWaysOfConditionsOfSeveralWaysAreTheirGroupsAddedUpTest {

    private static final TermPath X = TermPath.of("x");
    private static final TermPath Y = TermPath.of("y");

    /** An entry: a position asked to be one of some values, or one of several lists of entries. */
    private sealed interface Entry {}

    private record Ask(TermPath at, Set<Integer> values) implements Entry {}

    private record Choice(List<List<Entry>> alternatives) implements Entry {}

    /** What is asked so far is the values left at each position; none left at one closes it,
     *  said by that position. */
    private static final OneOfEach.Vocabulary<Entry, Map<TermPath, Set<Integer>>, TermPath>
            VALUES = new OneOfEach.Vocabulary<>() {

                @Override
                public List<List<Entry>> alternatives(Entry entry) {
                    return entry instanceof Choice choice ? choice.alternatives() : null;
                }

                @Override
                public Set<TermPath> positions(Entry entry) {
                    return entry instanceof Ask ask ? Set.of(ask.at()) : Set.of();
                }

                @Override
                public Map<TermPath, Set<Integer>> nothing() {
                    return Map.of();
                }

                @Override
                public Step<Map<TermPath, Set<Integer>>, TermPath> with(
                        Map<TermPath, Set<Integer>> so, Entry entry) {
                    if (!(entry instanceof Ask(TermPath at, Set<Integer> values))) {
                        return new Step.Held<>(so);
                    }
                    Set<Integer> left = new HashSet<>(so.getOrDefault(at, values));
                    left.retainAll(values);
                    if (left.isEmpty()) {
                        return new Step.Closed<>(at);
                    }
                    Map<TermPath, Set<Integer>> out = new LinkedHashMap<>(so);
                    out.put(at, left);
                    return new Step.Held<>(out);
                }
            };

    private static Ask ask(TermPath at, Integer... values) {
        return new Ask(at, Set.of(values));
    }

    private static Choice oneOf(Entry... alternatives) {
        List<List<Entry>> out = new ArrayList<>();
        for (Entry each : alternatives) {
            out.add(List.of(each));
        }
        return new Choice(out);
    }

    private static Walked<Entry, TermPath> walked(Entry... entries) {
        return OneOfEach.walk(List.of(entries), VALUES,
                CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT,
                CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG);
    }

    @SuppressWarnings("unchecked")
    private static Walked.Open<Entry, TermPath> open(Walked<Entry, TermPath> walked) {
        return assertInstanceOf(Walked.Open.class, walked, () -> "some way open: " + walked);
    }

    /** What each way asks, where every way chose every choice on it. */
    @SuppressWarnings("unchecked")
    private static List<List<Entry>> chosen(Walked.Open<Entry, TermPath> walked) {
        return walked.ways().stream().map(way -> ((OneOfEach.Way.Chosen<Entry>)
                assertInstanceOf(OneOfEach.Way.Chosen.class, way,
                        () -> "every choice chosen: " + walked)).entries()).toList();
    }

    /**
     * Two choices alike standing at two places are two choices, walked apart and handed on apart:
     * a way taking one of them one way and the other the other way says both, and neither is lost
     * for being equal to the other.
     */
    @Test
    @SuppressWarnings("unchecked")
    void twoChoicesAlikeAreBothSaidOfAWayThatTookThemApart() {
        Choice first = oneOf(ask(X, 1, 2), ask(X, 2, 3));
        Choice second = oneOf(ask(X, 1, 2), ask(X, 2, 3));
        assertEquals(first, second, "the two choices are alike");
        List<List<Integer>> taken = new ArrayList<>();
        for (OneOfEach.Way<Entry> way : open(walked(first, second)).ways()) {
            OneOfEach.Way.Chosen<Entry> chosen = assertInstanceOf(OneOfEach.Way.Chosen.class, way);
            assertEquals(2, chosen.choices().size(), () -> "both choices are said: " + chosen);
            taken.add(chosen.choices().stream().map(OneOfEach.Choice::alternative).toList());
        }
        assertTrue(taken.contains(List.of(0, 1)) && taken.contains(List.of(1, 0)),
                () -> "a way takes the two apart, either way round: " + taken);
    }

    /** Two conditions on two positions, every combination within the figure: each of them,
     *  since a row past both is along one. */
    @Test
    void conditionsOnPositionsApartWithinTheFigureAreEveryCombination() {
        Choice onX = oneOf(ask(X, 1), ask(X, 2), ask(X, 3));
        Choice onY = oneOf(ask(Y, 1), ask(Y, 2), ask(Y, 3));
        Walked.Open<Entry, TermPath> walked = open(walked(onX, onY));

        assertTrue(walked.everyWay(), () -> "every way a row takes: " + walked);
        List<List<Entry>> every = new ArrayList<>();
        for (int x = 1; x <= 3; x++) {
            for (int y = 1; y <= 3; y++) {
                every.add(List.of(ask(X, x), ask(Y, y)));
            }
        }
        assertEquals(every, chosen(walked));
    }

    /**
     * Two conditions on two positions whose combinations are more than the figure: each
     * alternative once, beside the other's first — and the figure, since a row may be along a
     * combination left out.
     */
    @Test
    void conditionsOnPositionsApartPastTheFigureAreEachAlternativeOnceAndTheFigure() {
        List<Entry> onX = new ArrayList<>();
        List<Entry> onY = new ArrayList<>();
        for (int each = 1; each <= 5; each++) {
            onX.add(ask(X, each));
            onY.add(ask(Y, each));
        }
        Walked.Open<Entry, TermPath> walked = open(walked(oneOf(onX.toArray(Entry[]::new)),
                oneOf(onY.toArray(Entry[]::new))));

        assertFalse(walked.everyWay(), () -> "not every way a row takes: " + walked);
        assertEquals(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG, walked.stoppedBy());
        List<List<Entry>> each = new ArrayList<>();
        each.add(List.of(ask(X, 1), ask(Y, 1)));
        for (int x = 2; x <= 5; x++) {
            each.add(List.of(ask(X, x), ask(Y, 1)));
        }
        for (int y = 2; y <= 5; y++) {
            each.add(List.of(ask(X, 1), ask(Y, y)));
        }
        assertEquals(each, chosen(walked));
    }

    /** Two conditions on one position are walked together, and a way they close is left out. */
    @Test
    void conditionsOnOnePositionAreTakenTogether() {
        Walked.Open<Entry, TermPath> walked = open(walked(oneOf(ask(X, 1), ask(X, 2)),
                oneOf(ask(X, 2), ask(X, 3))));

        assertEquals(List.of(List.of(ask(X, 2), ask(X, 2))), chosen(walked));
        assertTrue(walked.everyWay());
    }

    /**
     * Where every alternative of one group closes against what is asked beside it, nothing is
     * past the whole — whatever another group leaves open — and the way that closed first says
     * why.
     */
    @Test
    void aGroupWalkedToItsEndAndClosedClosesTheWhole() {
        Walked<Entry, TermPath> walked = walked(ask(X, 0), oneOf(ask(Y, 1), ask(Y, 2)),
                oneOf(ask(X, 1), ask(X, 2)));

        assertEquals(new Walked.Closed<>(List.of(ask(X, 0), ask(X, 1)), X), walked,
                "what is asked beside the conditions, the first alternative that closed, and"
                        + " the position nothing was left at");
    }

    /** What is asked beside the choices is judged by the walk too, with no choice on the way. */
    @Test
    void whatIsAskedBesideTheChoicesClosesTheWayWithNoChoiceOnIt() {
        Walked<Entry, TermPath> walked = walked(ask(X, 0), ask(Y, 1), ask(X, 1));

        assertEquals(new Walked.Closed<>(List.of(ask(X, 0), ask(Y, 1), ask(X, 1)), X), walked);
    }

    /** A condition nested in an alternative is chosen where it stands. */
    @Test
    void aConditionInsideAnAlternativeIsChosenWhereItStands() {
        Choice inner = oneOf(ask(X, 1), ask(X, 2));
        Choice outer = new Choice(List.of(List.of(ask(X, 1, 2), inner), List.of(ask(X, 3))));
        Walked.Open<Entry, TermPath> walked = open(walked(outer, ask(Y, 0)));

        assertEquals(List.of(
                        List.of(ask(X, 1, 2), ask(X, 1), ask(Y, 0)),
                        List.of(ask(X, 1, 2), ask(X, 2), ask(Y, 0)),
                        List.of(ask(X, 3), ask(Y, 0))),
                chosen(walked));
    }

    /**
     * A choice nested in an alternative is chosen where it stands however the vocabulary hands
     * the alternatives over — a vocabulary making them afresh each time it is asked included,
     * which hands back an entry equal to the one chosen and never the same one.
     */
    @Test
    void aNestedChoiceIsKeptWhereTheAlternativesAreMadeAfresh() {
        Choice inner = oneOf(ask(X, 1), ask(X, 2));
        Choice outer = new Choice(List.of(List.of(ask(X, 1, 2), inner), List.of(ask(X, 3))));
        Walked.Open<Entry, TermPath> walked = open(OneOfEach.walk(List.of(outer, ask(Y, 0)),
                AFRESH, CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT,
                CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG));

        assertEquals(List.of(
                        List.of(ask(X, 1, 2), ask(X, 1), ask(Y, 0)),
                        List.of(ask(X, 1, 2), ask(X, 2), ask(Y, 0)),
                        List.of(ask(X, 3), ask(Y, 0))),
                chosen(walked), "the nested choice's alternative is in each way past it");
    }

    /**
     * Where the looking one group did leaves none for the next, the ways the first found are
     * handed on — not no way at all — with the choice of the one not looked at left as it
     * stands, said to be left, and the figure that left it unlooked at.
     */
    @Test
    void aGroupLeftNothingToLookWithLeavesTheWaysBeforeIt() {
        List<Entry> entries = new ArrayList<>();
        int most = CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT.maximum();
        // Every alternative of the first is looked at, and only the last of them is open.
        entries.add(ask(X, most - 1));
        List<Entry> alternatives = new ArrayList<>();
        for (int each = 0; each < most; each++) {
            alternatives.add(ask(X, each));
        }
        entries.add(oneOf(alternatives.toArray(Entry[]::new)));
        Choice onY = oneOf(ask(Y, 1), ask(Y, 2));
        entries.add(onY);
        Walked.Open<Entry, TermPath> walked = open(walked(entries.toArray(Entry[]::new)));

        assertEquals(List.of(new OneOfEach.Way.LeftUnchosen<>(
                        List.of(ask(X, most - 1), ask(X, most - 1)), List.of(onY))), walked.ways(),
                "the open way of the first, with the choice not looked at left as it stands");
        assertEquals(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT, walked.stoppedBy());
    }

    /** {@link #VALUES}, handing the alternatives of a choice over as new entries each time. */
    private static final OneOfEach.Vocabulary<Entry, Map<TermPath, Set<Integer>>, TermPath>
            AFRESH = new OneOfEach.Vocabulary<>() {

                @Override
                public List<List<Entry>> alternatives(Entry entry) {
                    List<List<Entry>> asked = VALUES.alternatives(entry);
                    return asked == null ? null : asked.stream()
                            .map(way -> way.stream().map(each -> afresh(each)).toList())
                            .toList();
                }

                @Override
                public Set<TermPath> positions(Entry entry) {
                    return VALUES.positions(entry);
                }

                @Override
                public Map<TermPath, Set<Integer>> nothing() {
                    return VALUES.nothing();
                }

                @Override
                public Step<Map<TermPath, Set<Integer>>, TermPath> with(
                        Map<TermPath, Set<Integer>> so, Entry entry) {
                    return VALUES.with(so, entry);
                }
            };

    /** An entry equal to {@code entry} and not the same one. */
    private static Entry afresh(Entry entry) {
        return switch (entry) {
            case Ask(TermPath at, Set<Integer> values) -> new Ask(at, values);
            case Choice(List<List<Entry>> alternatives) -> new Choice(alternatives);
        };
    }

    /** More open ways than are looked along: the first of them, and the figure that cut them. */
    @Test
    void moreOpenWaysThanAreLookedAlongKeepTheFirstOnes() {
        int most = CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum();
        List<Entry> alternatives = new ArrayList<>();
        for (int each = 0; each <= most; each++) {
            alternatives.add(ask(X, each));
        }
        Walked.Open<Entry, TermPath> walked = open(walked(oneOf(
                alternatives.toArray(Entry[]::new))));

        assertEquals(most, walked.ways().size());
        assertEquals(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG, walked.stoppedBy());
    }

    /**
     * A walk the figure stopped before a group was looked at to its end proves nothing, however
     * many of its ways closed.
     */
    @Test
    void aWalkTheFigureStoppedProvesNothing() {
        List<Entry> entries = new ArrayList<>();
        int choices = Integer.numberOfTrailingZeros(Integer.highestOneBit(
                CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT.maximum()));
        for (int each = 0; each < choices; each++) {
            entries.add(oneOf(ask(X, 0, 1), ask(X, 0, 1, 2)));
        }
        entries.add(oneOf(ask(X, 5), ask(X, 6)));

        assertEquals(new Walked.Stopped<Entry, TermPath>(
                        CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT),
                walked(entries.toArray(Entry[]::new)), "nothing proved and no way found");
    }

    /** A way with no choice on it that holds together is the one way, and every way. */
    @Test
    void aWayWithNoChoiceIsTheOneWay() {
        Walked.Open<Entry, TermPath> walked = open(walked(ask(X, 0), ask(Y, 1)));

        assertEquals(List.of(List.of(ask(X, 0), ask(Y, 1))), chosen(walked));
        assertNull(walked.stoppedBy());
    }
}
