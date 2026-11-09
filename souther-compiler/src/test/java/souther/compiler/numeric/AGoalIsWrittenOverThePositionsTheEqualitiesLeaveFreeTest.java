package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two equalities over several positions together say what neither says alone: {@code x = a + b}
 * beside {@code y = b + a} is {@code x = y}. A goal is written over the positions the equalities
 * leave free, so a question that takes one rule as its premise is handed the one it needs. Where
 * the positions an equality is solved for are chosen among ones used alike, the goal is written
 * once for each choice.
 */
class AGoalIsWrittenOverThePositionsTheEqualitiesLeaveFreeTest {

    private static ExactRatio num(long whole) {
        return ExactRatio.of(whole);
    }

    private static Map<String, ExactRatio> weighing(Object... pairs) {
        Map<String, ExactRatio> out = new LinkedHashMap<>();
        for (int i = 0; i < pairs.length; i += 2) {
            out.put((String) pairs[i], num((Integer) pairs[i + 1]));
        }
        return out;
    }

    /** {@code Σ c·p = at}. */
    private static AffineConstraint.Equality<String> equality(Map<String, ExactRatio> coefs, long at) {
        return new AffineConstraint.Equality<>(new CanonicalForm<>(coefs), num(at));
    }

    private static final AffineConstraint.Equality<String> X_IS_A_AND_B =
            equality(weighing("x", 1, "a", -1, "b", -1), 0);

    private static final AffineConstraint.Equality<String> Y_IS_B_AND_A =
            equality(weighing("y", 1, "b", -1, "a", -1), 0);

    private static ReducedRules.Goal<String> goal(Map<String, ExactRatio> coefs, long constant) {
        return new ReducedRules.Goal<>(coefs, num(constant));
    }

    /** The goal with nothing left to prove. */
    private static final ReducedRules.Goal<String> NOUGHT = goal(Map.of(), 0);

    /** The goal as each reduction of the equalities writes it; none where there is none. */
    private static Set<ReducedRules.Goal<String>> through(
            List<AffineConstraint.Equality<String>> equalities, ReducedRules.Goal<String> goal) {
        List<AffineConstraint<String>> rules = new ArrayList<>(equalities);
        Set<ReducedRules.Goal<String>> out = new HashSet<>();
        for (ReducedRules<String> each : ReducedRules.of(rules, CanonicalOrder.asTheyAreSpelled())) {
            out.add(each.put(goal));
        }
        return out;
    }

    @Test
    void twoEqualitiesTogetherSayWhatNeitherSaysAlone() {
        assertEquals(Set.of(NOUGHT), through(
                List.of(X_IS_A_AND_B, Y_IS_B_AND_A), goal(weighing("x", 1, "y", -1), 0)));
    }

    @Test
    void theOrderTheyAreSaidInDoesNotMatter() {
        Set<ReducedRules.Goal<String>> one = through(
                List.of(X_IS_A_AND_B, Y_IS_B_AND_A), goal(weighing("x", 1, "y", -1), 0));
        Set<ReducedRules.Goal<String>> other = through(
                List.of(Y_IS_B_AND_A, X_IS_A_AND_B), goal(weighing("x", 1, "y", -1), 0));

        assertEquals(one, other);
    }

    @Test
    void theWritingIsTheSameWhicheverOrderTheEqualitiesAreSaidIn() {
        ReducedRules.Goal<String> goal = goal(weighing("x", 1, "c", 2), 1);
        AffineConstraint.Equality<String> third = equality(weighing("c", 1, "a", -1), 4);

        assertEquals(through(List.of(X_IS_A_AND_B, Y_IS_B_AND_A, third), goal),
                through(List.of(third, Y_IS_B_AND_A, X_IS_A_AND_B), goal));
    }

    @Test
    void anEqualityNoOtherIsSaidWithLeavesTheGoalSomethingToProve() {
        Set<ReducedRules.Goal<String>> freed = through(
                List.of(X_IS_A_AND_B), goal(weighing("x", 1, "y", -1), 0));

        assertTrue(freed.stream().noneMatch(each -> each.coefs().isEmpty()), freed.toString());
        assertTrue(freed.stream().anyMatch(each ->
                        each.coefs().keySet().equals(weighing("a", 1, "b", 1, "y", -1).keySet())),
                "solved for x, the goal is over a, b and y: " + freed);
    }

    @Test
    void theConstantsAreCarriedAlong() {
        assertEquals(Set.of(NOUGHT), through(
                List.of(equality(weighing("x", 1, "a", -1, "b", -1), 2),
                        equality(weighing("y", 1, "a", -1, "b", -1), 5)),
                goal(weighing("y", 1, "x", -1), -3)));
    }

    @Test
    void equalitiesThatAreOnlyDifferencesAreLeftToTheDomainThatHoldsThemExactly() {
        assertEquals(Set.of(), through(
                List.of(equality(weighing("x", 1, "a", -1), 2), equality(weighing("y", 1, "a", -1), 5)),
                goal(weighing("y", 1, "x", -1), -3)));
    }

    @Test
    void aGoalNoEqualityWeighsIsLeftAsItWas() {
        ReducedRules.Goal<String> asked = goal(weighing("c", 1, "d", -1), 0);

        assertEquals(Set.of(asked), through(List.of(X_IS_A_AND_B), asked));
        assertEquals(Set.of(), through(List.of(), goal(weighing("x", 1), 0)), "nothing to leave free");
    }

    @Test
    void anEqualityJoinedToTheGoalThroughAnotherIsSolvedAndOneNothingJoinsIsNot() {
        AffineConstraint.Equality<String> y_is_c = equality(weighing("y", 1, "c", -1), 0);
        AffineConstraint.Equality<String> c_is_a_and_b = equality(weighing("c", 1, "a", -1, "b", -1), 0);
        AffineConstraint.Equality<String> apart = equality(weighing("e", 1, "f", -1), 7);

        assertEquals(Set.of(NOUGHT), through(
                List.of(apart, X_IS_A_AND_B, y_is_c, c_is_a_and_b),
                goal(weighing("x", 1, "y", -1), 0)));
        assertEquals(Set.of(), through(List.of(apart), goal(weighing("x", 1, "y", -1), 0)));
    }

    @Test
    void twoSumsOfTwoPositionsAreSolvedTogether() {
        // a + b = 10 and a + c = 10 say b = c, and neither is a difference of two positions.
        assertEquals(Set.of(NOUGHT), through(
                List.of(equality(weighing("a", 1, "b", 1), 10), equality(weighing("a", 1, "c", 1), 10)),
                goal(weighing("b", 1, "c", -1), 0)));
    }

    @Test
    void anEqualityGivenTwiceIsGivenOnce() {
        assertEquals(Set.of(NOUGHT), through(
                List.of(X_IS_A_AND_B, Y_IS_B_AND_A, X_IS_A_AND_B),
                goal(weighing("x", 1, "y", -1), 0)));
    }
}
