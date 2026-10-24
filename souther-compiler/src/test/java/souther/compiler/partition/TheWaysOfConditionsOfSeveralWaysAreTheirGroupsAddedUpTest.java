package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.partition.OneOfEach.Step;
import souther.compiler.partition.OneOfEach.Walked;

import java.util.ArrayList;
import java.util.Arrays;
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
     * alternative once, beside the other's first, the second alternatives of both before the
     * third of either — and the figure, since a row may be along a combination left out.
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
        for (int number = 2; number <= 5; number++) {
            each.add(List.of(ask(X, number), ask(Y, 1)));
            each.add(List.of(ask(X, 1), ask(Y, number)));
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
     * More ways that hold together in one group than are looked along: every alternative of
     * every choice is still in a way handed on. The ways the walk finds first differ only in the
     * choices it comes to last, so a way past the second alternative of the first choice, which
     * only the ways after those take, is the one a row at a border may need.
     */
    @Test
    void moreWaysInOneGroupThanAreLookedAlongStillTakeEachAlternativeOnce() {
        List<Entry> entries = new ArrayList<>();
        entries.add(oneOf(ask(X, 1), ask(X, 2)));
        for (int each = 0; each < 5; each++) {
            entries.add(oneOf(ask(X, 1, 2), ask(X, 1, 2, 10 + each)));
        }
        Walked.Open<Entry, TermPath> walked = open(walked(entries.toArray(Entry[]::new)));

        assertEquals(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG, walked.stoppedBy());
        List<List<Entry>> ways = chosen(walked);
        assertTrue(ways.size() <= CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum(),
                () -> "no more than the figure: " + ways.size());
        assertTrue(ways.stream().anyMatch(way -> way.getFirst().equals(ask(X, 1))),
                () -> "the first alternative of the first choice: " + ways);
        assertTrue(ways.stream().anyMatch(way -> way.getFirst().equals(ask(X, 2))),
                () -> "the second alternative of the first choice: " + ways);
        for (int each = 0; each < 5; each++) {
            Entry second = ask(X, 1, 2, 10 + each);
            assertTrue(ways.stream().anyMatch(way -> way.contains(second)),
                    () -> "the second alternative of a later choice, " + second + ": " + ways);
        }
    }

    /**
     * An alternative of a choice nested inside another is looked for through the alternative of
     * the outer choice that holds it. The ways the walk finds first all take the outer choice's
     * first alternative, which does not hold the inner choice, so a way taking the inner choice's
     * second alternative is one the outer choice's second alternative leads to.
     */
    @Test
    void anAlternativeOfANestedChoiceIsLookedForThroughTheAlternativeThatHoldsIt() {
        Choice inner = oneOf(ask(X, 1), ask(X, 2));
        Choice outer = new Choice(List.of(List.of(ask(X, 1, 2)), List.of(ask(X, 1, 2), inner)));
        List<Entry> entries = new ArrayList<>();
        entries.add(outer);
        for (int each = 0; each < 5; each++) {
            entries.add(oneOf(ask(X, 1, 2), ask(X, 1, 2, 10 + each)));
        }
        Walked.Open<Entry, TermPath> walked = open(walked(entries.toArray(Entry[]::new)));

        List<List<Entry>> ways = chosen(walked);
        assertTrue(ways.stream().anyMatch(way -> way.contains(ask(X, 1))),
                () -> "the inner choice's first alternative: " + ways);
        assertTrue(ways.stream().anyMatch(way -> way.contains(ask(X, 2))),
                () -> "the inner choice's second alternative: " + ways);
        assertEquals(ways.size(), new HashSet<>(ways).size(), () -> "no way twice: " + ways);
    }

    /**
     * Where a choice's alternatives are more than the figure lets through, the later ones are
     * the ones left: no choice's alternative is passed over for another's, and the figure says
     * that the rest was not looked at.
     */
    @Test
    void pastTheFigureNoAlternativeIsPassedOverForALaterOne() {
        int limit = CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum();
        List<Entry> alternatives = new ArrayList<>();
        for (int each = 0; each <= limit; each++) {
            alternatives.add(ask(X, each));
        }
        Walked.Open<Entry, TermPath> walked = open(walked(oneOf(
                alternatives.toArray(Entry[]::new))));

        List<List<Entry>> ways = chosen(walked);
        assertEquals(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG, walked.stoppedBy());
        assertEquals(limit, ways.size());
        assertEquals(alternatives.subList(0, limit),
                ways.stream().map(List::getFirst).toList());
    }

    /**
     * A choice nested in the third alternative of another is not met until that alternative is
     * looked for, which is after the second alternative of every choice met before it: its own
     * second alternative is still owed a way.
     */
    @Test
    void aNestedChoiceMetAtTheThirdAlternativeGetsBothOfItsAlternatives() {
        Choice inner = oneOf(ask(X, 1), ask(X, 2));
        Choice outer = new Choice(List.of(List.of(ask(X, 1, 2)), List.of(ask(X, 1, 2)),
                List.of(ask(X, 1, 2), inner)));
        List<Entry> entries = new ArrayList<>();
        entries.add(outer);
        for (int each = 0; each < 4; each++) {
            entries.add(oneOf(ask(X, 1, 2), ask(X, 1, 2, 10 + each)));
        }
        Walked.Open<Entry, TermPath> walked = open(walked(entries.toArray(Entry[]::new)));

        List<List<Entry>> ways = chosen(walked);
        assertTrue(ways.stream().anyMatch(way -> way.contains(ask(X, 1))),
                () -> "the inner choice's first alternative: " + ways);
        assertTrue(ways.stream().anyMatch(way -> way.contains(ask(X, 2))),
                () -> "the inner choice's second alternative: " + ways);
    }

    /**
     * Independent groups whose ways are more than the figure let through together: the second
     * alternative of the small group is not passed over for the later alternatives of the large
     * one, as it is not within a group.
     */
    @Test
    void anAlternativeOfASmallGroupIsNotPassedOverForTheLaterOnesOfALargeGroup() {
        int limit = CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum();
        List<Entry> alternatives = new ArrayList<>();
        for (int each = 0; each <= limit; each++) {
            alternatives.add(ask(X, each));
        }
        Walked.Open<Entry, TermPath> walked = open(walked(
                oneOf(alternatives.toArray(Entry[]::new)), oneOf(ask(Y, 1), ask(Y, 2))));

        List<List<Entry>> ways = chosen(walked);
        assertEquals(limit, ways.size());
        assertTrue(ways.stream().anyMatch(way -> way.contains(ask(Y, 1))), () -> "y 1: " + ways);
        assertTrue(ways.stream().anyMatch(way -> way.contains(ask(Y, 2))), () -> "y 2: " + ways);
        assertTrue(ways.stream().anyMatch(way -> way.contains(ask(X, 1))), () -> "x 1: " + ways);
    }

    /**
     * Choices turning on one position whose ways are far more than the figure: the first way,
     * then the second alternative of each choice beside the first of every other, the choices in
     * the order the walk came to them and no more than the figure.
     */
    @Test
    void manyChoicesGetTheirSecondAlternativeOneBesideTheFirstsInTheOrderTheyAreMet() {
        int limit = CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum();
        List<Entry> entries = new ArrayList<>();
        for (int each = 0; each < limit + 4; each++) {
            entries.add(oneOf(ask(X, 1, 2), ask(X, 1, 2, 10 + each)));
        }
        Walked.Open<Entry, TermPath> walked = open(walked(entries.toArray(Entry[]::new)));

        List<List<Entry>> ways = chosen(walked);
        assertEquals(limit, ways.size());
        for (int way = 0; way < limit; way++) {
            List<Entry> expected = new ArrayList<>();
            for (int each = 0; each < entries.size(); each++) {
                expected.add(way > 0 && each == way - 1 ? ask(X, 1, 2, 10 + each) : ask(X, 1, 2));
            }
            assertEquals(expected, ways.get(way), "way " + way);
        }
    }

    /**
     * What is done to give every alternative a way does not take the looking a later group is
     * owed: the group on another position is looked at whole, however much the first group's
     * alternatives were looked for.
     */
    @Test
    void lookingForTheAlternativesOfOneGroupLeavesTheLookingOfTheNextGroup() {
        List<Entry> entries = new ArrayList<>();
        int choices = CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT.maximum() / 8;
        for (int each = 0; each < choices; each++) {
            entries.add(oneOf(ask(X, 1, 2), ask(X, 1, 2, 10 + each)));
        }
        Choice onY = oneOf(ask(Y, 1), ask(Y, 2));
        entries.add(onY);
        Walked.Open<Entry, TermPath> walked = open(walked(entries.toArray(Entry[]::new)));

        assertFalse(walked.ways().isEmpty());
        for (OneOfEach.Way<Entry> way : walked.ways()) {
            assertInstanceOf(OneOfEach.Way.Chosen.class, way,
                    () -> "the choice on y is chosen in every way: " + way);
        }
    }

    /**
     * Whatever the shape of the groups and the choices, the ways handed on are no more than the
     * figure and none twice, the first way is the one that takes every first alternative, and the
     * alternatives are not passed over for one another: for every number up to which the
     * alternatives of all the choices, one way each beside the firsts, fit in the figure, every
     * alternative up to that number has a way.
     *
     * <p>Over every shape of three choices with up to nine alternatives each, on one position and
     * on two, so that the shapes where the ways are more than the figure and the ones where they
     * are fewer are both there.
     */
    @Test
    void whateverTheShapeTheWaysAreWithinTheFigureOnceAndFairToTheAlternatives() {
        int limit = CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum();
        for (int onTwo = 0; onTwo < 2; onTwo++) {
            for (int a = 1; a <= 9; a++) {
                for (int b = 1; b <= 9; b++) {
                    for (int c = 1; c <= 9; c++) {
                        int[] sizes = {a, b, c};
                        TermPath[] ats = {X, onTwo == 1 ? Y : X, X};
                        int[] froms = {10, 110, 210};
                        List<Entry> entries = new ArrayList<>();
                        for (int each = 0; each < 3; each++) {
                            entries.add(alternativesOn(ats[each], froms[each], sizes[each]));
                        }
                        String shape = Arrays.toString(sizes) + (onTwo == 1 ? " on two" : " on one");
                        List<List<Entry>> ways = chosen(open(walked(entries.toArray(Entry[]::new))));

                        assertTrue(ways.size() <= limit, shape + ": no more than the figure");
                        assertEquals(ways.size(), new HashSet<>(ways).size(),
                                shape + ": no way twice");
                        assertEquals(List.of(ask(ats[0], 1, 2, froms[0]),
                                        ask(ats[1], 1, 2, froms[1]), ask(ats[2], 1, 2, froms[2])),
                                ways.getFirst(), shape + ": the first way takes every first");
                        for (int number = 1; number < 9; number++) {
                            int owed = 1;
                            for (int size : sizes) {
                                owed += Math.min(size - 1, number);
                            }
                            if (owed > limit) {
                                break;
                            }
                            for (int each = 0; each < 3; each++) {
                                for (int alternative = 1;
                                        alternative <= Math.min(sizes[each] - 1, number);
                                        alternative++) {
                                    Entry wanted = ask(ats[each], 1, 2, froms[each] + alternative);
                                    assertTrue(ways.stream().anyMatch(way -> way.contains(wanted)),
                                            shape + ": " + wanted + " has a way");
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /** A choice of {@code count} alternatives, each asking {@code at} to be 1 or 2 or a value of
     *  its own, from {@code from} up. Any alternatives of choices on one position hold together. */
    private static Choice alternativesOn(TermPath at, int from, int count) {
        List<Entry> out = new ArrayList<>();
        for (int each = 0; each < count; each++) {
            out.add(ask(at, 1, 2, from + each));
        }
        return oneOf(out.toArray(Entry[]::new));
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
