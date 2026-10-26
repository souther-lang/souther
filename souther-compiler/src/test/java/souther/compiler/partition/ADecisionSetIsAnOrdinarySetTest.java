package souther.compiler.partition;

import souther.compiler.inputs.TermPath;

import org.junit.jupiter.api.Test;

import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * The decisions of a combination are a set like any other: equal to every set that holds the same
 * decisions, from either side, and hashing as a set does.
 *
 * <p>The decision is written out in full because this package declares a {@code Condition} of its
 * own.
 */
class ADecisionSetIsAnOrdinarySetTest {

    private static final souther.compiler.reading.Condition A =
            new souther.compiler.reading.Condition.Case(TermPath.of("a"), List.of("X"));
    private static final souther.compiler.reading.Condition B =
            new souther.compiler.reading.Condition.Case(TermPath.of("b"), List.of("Y"));
    private static final souther.compiler.reading.Condition C =
            new souther.compiler.reading.Condition.Case(TermPath.of("c"), List.of("Z"));

    @Test
    void itIsEqualToAnOrdinarySetFromEitherSide() {
        Set<souther.compiler.reading.Condition> ordinary = Set.of(A, B);
        DecisionSet decisions = DecisionSet.of(ordinary);

        assertEquals(ordinary, decisions);
        assertEquals(decisions, ordinary);
        assertEquals(ordinary.hashCode(), decisions.hashCode());
    }

    @Test
    void itDoesNotDependOnTheOrderTheDecisionsWereGivenIn() {
        Set<souther.compiler.reading.Condition> forwards = new LinkedHashSet<>(List.of(A, B, C));
        Set<souther.compiler.reading.Condition> backwards = new LinkedHashSet<>(List.of(C, B, A));

        assertEquals(DecisionSet.of(forwards), DecisionSet.of(backwards));
        assertEquals(DecisionSet.of(forwards).hashCode(), DecisionSet.of(backwards).hashCode());
    }

    @Test
    void itIsNotEqualToASetOfOtherDecisions() {
        assertNotEquals(DecisionSet.of(Set.of(A, B)), Set.of(A, C));
        assertNotEquals(Set.of(A, C), DecisionSet.of(Set.of(A, B)));
        assertNotEquals(DecisionSet.of(Set.of(A, B)), DecisionSet.of(Set.of(A)));
    }

    @Test
    void madeFromTheHashesAGroupAlreadyHoldsItIsTheSameSetOnce() {
        Map<souther.compiler.reading.Condition, Integer> hashes = new IdentityHashMap<>();
        DecisionSet made = DecisionSet.of(List.of(A, B, A), hashes);

        assertEquals(Set.of(A, B), made);
        assertEquals(Set.of(A, B).hashCode(), made.hashCode());
        assertEquals(2, made.size());
        assertEquals(Set.of(A, B), hashes.keySet());
    }
}
