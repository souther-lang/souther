package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Equalities that share no position are solved apart. A set that contradicts itself, or takes more
 * work than {@link ReducedRules#MOST_UPDATES} allows, is left as the equalities it was, and the
 * others are solved all the same.
 */
class ASetOfEqualitiesThatCannotBeSolvedCostsTheOthersNothingTest {

    private static final CanonicalOrder<String> ORDER = CanonicalOrder.asTheyAreSpelled();

    private static Map<String, ExactRatio> weighing(Object... pairs) {
        Map<String, ExactRatio> out = new LinkedHashMap<>();
        for (int i = 0; i < pairs.length; i += 2) {
            out.put((String) pairs[i], ExactRatio.of((Integer) pairs[i + 1]));
        }
        return out;
    }

    private static AffineConstraint<String> equality(Map<String, ExactRatio> coefs, long at) {
        return new AffineConstraint.Equality<>(new CanonicalForm<>(coefs), ExactRatio.of(at));
    }

    private static ReducedRules.Goal<String> goal(String position) {
        return new ReducedRules.Goal<>(weighing(position, 1), ExactRatio.ZERO);
    }

    /** {@code x = a + b}, a set of its own. */
    private static final AffineConstraint<String> SMALL = equality(weighing("x", 1, "a", -1, "b", -1), 0);

    /**
     * A chain {@code p0 = p1 + q0, p1 = p2 + q1, …}, one set whose solving updates a weight for
     * every pair of equalities and so outgrows any bound on the work.
     */
    private static List<AffineConstraint<String>> chain(int length) {
        List<AffineConstraint<String>> out = new ArrayList<>();
        for (int i = 0; i < length; i++) {
            out.add(equality(weighing("p" + i, 1, "p" + (i + 1), -1, "q" + i, -1), 0));
        }
        return out;
    }

    @Test
    void aSetTakingMoreWorkThanTheBoundIsLeftAsItWasAndTheOthersAreSolved() {
        List<AffineConstraint<String>> rules = new ArrayList<>(chain(400));
        rules.add(SMALL);

        ReducedRules<String> reduced = solvingXForX(ReducedRules.of(rules, ORDER));

        assertEquals(goal("p0"), reduced.put(goal("p0")), "the chain is left unsolved");
        assertEquals(400, reduced.rules().stream().filter(each -> each.rel() == Rel.EQ).count(),
                "and its equalities stay rules");
    }

    @Test
    void aChainWithinTheBoundIsSolved() {
        List<ReducedRules<String>> reduced = ReducedRules.of(new ArrayList<>(chain(3)), ORDER);

        assertTrue(!reduced.isEmpty());
        assertTrue(reduced.stream().allMatch(each -> each.rules().isEmpty()), reduced.toString());
    }

    /**
     * The last equation of a chain, written over what the others solved, names every end of it
     * alike, and each is a position it may be solved for. Solved for the first few of them in the
     * order of the names, which they were would be the names' choice, so past the bound none is.
     */
    @Test
    void aChainWithMoreWaysOfSolvingItThanTheBoundHasNoReduction() {
        assertEquals(List.of(), ReducedRules.of(new ArrayList<>(chain(20)), ORDER));
    }

    @Test
    void aSetThatContradictsItselfIsLeftAsItWasAndTheOthersAreSolved() {
        List<AffineConstraint<String>> rules = List.of(
                equality(weighing("u", 1, "c", -1, "d", -1), 0),
                equality(weighing("u", 1, "c", -1, "d", -1), 1),
                SMALL);

        ReducedRules<String> reduced = solvingXForX(ReducedRules.of(rules, ORDER));

        assertEquals(goal("u"), reduced.put(goal("u")));
        assertEquals(2, reduced.rules().size(), "the two that contradict stay rules");
    }

    @Test
    void whereNoSetCanBeSolvedThereIsNothingToLeaveFree() {
        assertEquals(List.of(), ReducedRules.of(List.of(
                equality(weighing("u", 1, "c", -1, "d", -1), 0),
                equality(weighing("u", 1, "c", -1, "d", -1), 1)), ORDER));
    }

    /**
     * A chain whose every equality is solved for one position and no other: a descent of one level
     * each and a single way. What holds the descent to a depth is the number of equalities in a set,
     * which the ways counted do not, since an equality that is a combination of the others takes a
     * level and gives no choice at all.
     */
    private static List<AffineConstraint<String>> aChainOfOneWayOfSolvingIt(int length) {
        List<AffineConstraint<String>> out = new ArrayList<>();
        for (int i = 0; i < length; i++) {
            out.add(equality(weighing("p" + i, 1, "p" + (i + 1), -1, "q" + i, -(i + 2)), 0));
        }
        return out;
    }

    @Test
    void aSetOfNoMoreEqualitiesThanAreLookedThroughHasItsWayOfSolvingIt() {
        assertEquals(1, ReducedRules.of(
                aChainOfOneWayOfSolvingIt(ReducedRules.MOST_EQUATIONS), ORDER).size());
    }

    @Test
    void aSetOfMoreEqualitiesThanAreLookedThroughIsLeftAsTheEqualitiesItWas() {
        assertEquals(List.of(), ReducedRules.of(
                aChainOfOneWayOfSolvingIt(ReducedRules.MOST_EQUATIONS + 1), ORDER));
    }

    /**
     * The reduction of {@code x = a + b} that solves it for {@code x}, one of the three there are
     * for it: the positions of that equality are used alike.
     */
    private static ReducedRules<String> solvingXForX(List<ReducedRules<String>> reductions) {
        assertEquals(3, reductions.size());
        return reductions.stream()
                .filter(each -> Map.of("a", ExactRatio.ONE, "b", ExactRatio.ONE)
                        .equals(each.put(goal("x")).coefs()))
                .findFirst().orElseThrow();
    }
}
