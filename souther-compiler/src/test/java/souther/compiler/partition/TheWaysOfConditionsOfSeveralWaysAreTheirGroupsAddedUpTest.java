package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The ways conditions of several ways come to are the ways of each group of them that turns on
 * positions in common, added up and not multiplied — and a proof that nothing is past them comes
 * only from a group walked to its end.
 */
class TheWaysOfConditionsOfSeveralWaysAreTheirGroupsAddedUpTest {

    private static final TermPath X = TermPath.of("x");
    private static final TermPath Y = TermPath.of("y");

    /** An entry: a position asked to be one of some values, or one of several lists of entries. */
    private sealed interface Entry {}

    private record Ask(TermPath at, Set<Integer> values) implements Entry {}

    private record Choice(List<List<Entry>> alternatives) implements Entry {}

    /** What is asked so far is the values left at each position; none left closes it. */
    private static final OneOfEach.Vocabulary<Entry, Map<TermPath, Set<Integer>>> VALUES =
            new OneOfEach.Vocabulary<>() {

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
                public Map<TermPath, Set<Integer>> with(Map<TermPath, Set<Integer>> so,
                                                        Entry entry) {
                    if (!(entry instanceof Ask(TermPath at, Set<Integer> values))) {
                        return so;
                    }
                    Set<Integer> left = new HashSet<>(so.getOrDefault(at, values));
                    left.retainAll(values);
                    if (left.isEmpty()) {
                        return null;
                    }
                    Map<TermPath, Set<Integer>> out = new LinkedHashMap<>(so);
                    out.put(at, left);
                    return out;
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

    private static OneOfEach.Walked<Entry> walked(Entry... entries) {
        return OneOfEach.walk(List.of(entries), VALUES,
                CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT,
                CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG);
    }

    /** Two conditions on two positions: each alternative once, beside the other's first. */
    @Test
    void conditionsOnPositionsApartAreEachAlternativeOnce() {
        Choice onX = oneOf(ask(X, 1), ask(X, 2), ask(X, 3));
        Choice onY = oneOf(ask(Y, 1), ask(Y, 2), ask(Y, 3));
        OneOfEach.Walked<Entry> walked = walked(onX, onY);

        assertTrue(walked.everyWay(), () -> "every way looked at: " + walked);
        assertEquals(List.of(
                        List.of(ask(X, 1), ask(Y, 1)),
                        List.of(ask(X, 2), ask(Y, 1)),
                        List.of(ask(X, 3), ask(Y, 1)),
                        List.of(ask(X, 1), ask(Y, 2)),
                        List.of(ask(X, 1), ask(Y, 3))),
                walked.ways(), "the alternatives added up, and not their nine ways together");
    }

    /** Two conditions on one position are walked together, and a way they close is left out. */
    @Test
    void conditionsOnOnePositionAreTakenTogether() {
        OneOfEach.Walked<Entry> walked = walked(oneOf(ask(X, 1), ask(X, 2)),
                oneOf(ask(X, 2), ask(X, 3)));

        assertEquals(List.of(List.of(ask(X, 2), ask(X, 2))), walked.ways());
        assertTrue(walked.everyWay());
    }

    /**
     * Where every alternative of one group closes against what is asked beside it, nothing is
     * past the whole — whatever another group leaves open — and the way that closed first says
     * why.
     */
    @Test
    void aGroupWalkedToItsEndAndClosedClosesTheWhole() {
        OneOfEach.Walked<Entry> walked = walked(ask(X, 0), oneOf(ask(Y, 1), ask(Y, 2)),
                oneOf(ask(X, 1), ask(X, 2)));

        assertEquals(List.of(), walked.ways());
        assertEquals(List.of(ask(X, 0), ask(X, 1)), walked.closedBy(),
                "what is asked beside the conditions, and the first alternative that closed");
    }

    /** A condition nested in an alternative is chosen where it stands. */
    @Test
    void aConditionInsideAnAlternativeIsChosenWhereItStands() {
        Choice inner = oneOf(ask(X, 1), ask(X, 2));
        Choice outer = new Choice(List.of(List.of(ask(X, 1, 2), inner), List.of(ask(X, 3))));
        OneOfEach.Walked<Entry> walked = walked(outer, ask(Y, 0));

        assertEquals(List.of(
                        List.of(ask(X, 1, 2), ask(X, 1), ask(Y, 0)),
                        List.of(ask(X, 1, 2), ask(X, 2), ask(Y, 0)),
                        List.of(ask(X, 3), ask(Y, 0))),
                walked.ways());
    }

    /** More open ways than are looked along: the first of them, and the figure that cut them. */
    @Test
    void moreOpenWaysThanAreLookedAlongKeepTheFirstOnes() {
        int most = CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum();
        List<Entry> alternatives = new ArrayList<>();
        for (int each = 0; each <= most; each++) {
            alternatives.add(ask(X, each));
        }
        OneOfEach.Walked<Entry> walked = walked(oneOf(alternatives.toArray(Entry[]::new)));

        assertEquals(most, walked.ways().size());
        assertEquals(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG, walked.stoppedBy());
        assertNull(walked.closedBy());
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
        OneOfEach.Walked<Entry> walked = walked(entries.toArray(Entry[]::new));

        assertEquals(List.of(), walked.ways());
        assertNull(walked.closedBy(), () -> "nothing proved: " + walked);
        assertNotNull(walked.stoppedBy());
        assertEquals(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT, walked.stoppedBy());
    }
}
