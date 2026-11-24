package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An equality and a hole are one rule written either way round, and a bound has a side that is what
 * it says: the reduction of the rules is the same whichever way an equality or a hole was written,
 * and keeps the side and the strictness of a bound.
 */
class ARulesReductionIsTheSameWhicheverWayEachRuleIsWrittenTest {

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

    private static AffineConstraint<String> hole(Map<String, ExactRatio> coefs, long at) {
        return new AffineConstraint.Disequality<>(new CanonicalForm<>(coefs), ExactRatio.of(at));
    }

    private static AffineConstraint<String> below(Map<String, ExactRatio> coefs, ExactCut bound) {
        return new AffineConstraint.HalfSpace<>(new CanonicalForm<>(coefs), bound);
    }

    private static ReducedRules.Goal<String> goal(Map<String, ExactRatio> coefs) {
        return new ReducedRules.Goal<>(coefs, ExactRatio.ZERO);
    }

    /**
     * {@code x - 2y = 3} and {@code -x + 2y = -3} are one equality, and one of the two positions
     * is solved for whichever was written: the weights are not what the positions are used as.
     */
    @Test
    void anEqualityWrittenTheOtherWayRoundIsSolvedForTheSamePosition() {
        List<ReducedRules<String>> one = ReducedRules.of(
                List.of(equality(weighing("x", 1, "y", -2), 3)), ORDER);
        List<ReducedRules<String>> other = ReducedRules.of(
                List.of(equality(weighing("x", -1, "y", 2), -3)), ORDER);

        assertEquals(1, one.size());
        assertEquals(1, other.size());
        assertEquals(one.getFirst().put(goal(weighing("x", 1))),
                other.getFirst().put(goal(weighing("x", 1))));
        assertEquals(one.getFirst().put(goal(weighing("y", 1))),
                other.getFirst().put(goal(weighing("y", 1))));
    }

    @Test
    void aHoleWrittenTheOtherWayRoundIsReducedTheSame() {
        List<AffineConstraint<String>> one = List.of(equality(weighing("x", 1, "a", -1, "b", -1), 0),
                hole(weighing("a", 1, "b", -2), 3));
        List<AffineConstraint<String>> other = List.of(equality(weighing("x", 1, "a", -1, "b", -1), 0),
                hole(weighing("a", -1, "b", 2), -3));

        assertEquals(rulesOf(ReducedRules.of(one, ORDER)), rulesOf(ReducedRules.of(other, ORDER)));
    }

    /** What each reduction says, as a set: the reductions are not in an order. */
    private static Set<List<ReducedRules.Rule<String>>> rulesOf(List<ReducedRules<String>> each) {
        return each.stream().map(ReducedRules::rules).collect(Collectors.toSet());
    }

    /** Whether the domain holds an equality exactly as a difference does not turn on its writing. */
    @Test
    void anEqualityTheDomainHoldsExactlyIsLeftToItWhicheverWayItIsWritten() {
        assertEquals(List.of(), ReducedRules.of(List.of(equality(weighing("x", 1, "y", -1), 2)), ORDER));
        assertEquals(List.of(), ReducedRules.of(List.of(equality(weighing("x", -1, "y", 1), -2)), ORDER));
        assertEquals(List.of(), ReducedRules.of(List.of(equality(weighing("x", 1), 3)), ORDER));
        assertEquals(List.of(), ReducedRules.of(List.of(equality(weighing("x", -1), -3)), ORDER));
    }

    /** What a bound says is which side it holds a sum on, and that is kept. */
    @Test
    void aBoundKeepsItsSideAndItsStrictness() {
        List<AffineConstraint<String>> rules = List.of(
                equality(weighing("x", 1, "a", -1, "b", -1), 0),
                below(weighing("x", 1, "c", -1), ExactCut.exclusive(ExactRatio.of(5))),
                below(weighing("x", -1, "d", 1), ExactCut.inclusive(ExactRatio.of(2))));

        List<ReducedRules.Rule<String>> reduced = ReducedRules.of(rules, ORDER).getFirst().rules();

        assertEquals(2, reduced.size());
        assertTrue(reduced.stream().anyMatch(each -> each.rel() == Rel.LT), reduced.toString());
        assertTrue(reduced.stream().anyMatch(each -> each.rel() == Rel.LE), reduced.toString());
    }

    /** A hole is a hole over the free positions: not a bound, and not dropped. */
    @Test
    void aHoleIsStillAHoleOverTheFreePositions() {
        List<AffineConstraint<String>> rules = List.of(
                equality(weighing("x", 1, "a", -1, "b", -1), 0),
                hole(weighing("x", 1, "c", -1), 3));

        List<ReducedRules.Rule<String>> reduced = ReducedRules.of(rules, ORDER).getFirst().rules();

        assertEquals(1, reduced.size());
        assertEquals(Rel.NE, reduced.getFirst().rel());
        assertTrue(!reduced.getFirst().coefs().containsKey("x"), reduced.toString());
    }
}
