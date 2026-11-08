package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Two equalities over several positions together say what neither says alone: {@code x = a + b}
 * beside {@code y = b + a} is {@code x = y}. A goal is written over the positions the equalities
 * leave free, so a question that takes one rule as its premise is handed the one it needs.
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

    private static EqualityElimination.Goal<String> goal(Map<String, ExactRatio> coefs, long constant) {
        return new EqualityElimination.Goal<>(coefs, num(constant));
    }

    private static EqualityElimination.Goal<String> through(
            List<AffineConstraint.Equality<String>> equalities, EqualityElimination.Goal<String> goal) {
        return EqualityElimination.through(equalities, goal, CanonicalOrder.asTheyAreSpelled());
    }

    @Test
    void twoEqualitiesTogetherSayWhatNeitherSaysAlone() {
        EqualityElimination.Goal<String> freed = through(
                List.of(X_IS_A_AND_B, Y_IS_B_AND_A), goal(weighing("x", 1, "y", -1), 0));

        assertNotNull(freed);
        assertEquals(Map.of(), freed.coefs());
        assertEquals(num(0), freed.constant());
    }

    @Test
    void theOrderTheyAreSaidInDoesNotMatter() {
        EqualityElimination.Goal<String> one = through(
                List.of(X_IS_A_AND_B, Y_IS_B_AND_A), goal(weighing("x", 1, "y", -1), 0));
        EqualityElimination.Goal<String> other = through(
                List.of(Y_IS_B_AND_A, X_IS_A_AND_B), goal(weighing("x", 1, "y", -1), 0));

        assertEquals(one, other);
    }

    @Test
    void theWritingIsTheSameWhicheverOrderTheEqualitiesAreSaidIn() {
        EqualityElimination.Goal<String> goal = goal(weighing("x", 1, "c", 2), 1);
        AffineConstraint.Equality<String> third = equality(weighing("c", 1, "a", -1), 4);

        assertEquals(through(List.of(X_IS_A_AND_B, Y_IS_B_AND_A, third), goal),
                through(List.of(third, Y_IS_B_AND_A, X_IS_A_AND_B), goal));
    }

    @Test
    void anEqualityNoOtherIsSaidWithLeavesTheGoalSomethingToProve() {
        EqualityElimination.Goal<String> freed = through(
                List.of(X_IS_A_AND_B), goal(weighing("x", 1, "y", -1), 0));

        assertEquals(weighing("a", 1, "b", 1, "y", -1).keySet(), freed.coefs().keySet());
    }

    @Test
    void theConstantsAreCarriedAlong() {
        EqualityElimination.Goal<String> freed = through(
                List.of(equality(weighing("x", 1, "a", -1), 2), equality(weighing("y", 1, "a", -1), 5)),
                goal(weighing("y", 1, "x", -1), -3));

        assertEquals(Map.of(), freed.coefs());
        assertEquals(num(0), freed.constant());
    }

    @Test
    void aGoalNoEqualityWeighsIsLeftAsItWas() {
        assertNull(through(List.of(X_IS_A_AND_B), goal(weighing("c", 1, "d", -1), 0)));
        assertNull(through(List.of(), goal(weighing("x", 1), 0)));
    }

    @Test
    void anEqualityGivenTwiceIsGivenOnce() {
        EqualityElimination.Goal<String> freed = through(
                List.of(X_IS_A_AND_B, Y_IS_B_AND_A, X_IS_A_AND_B),
                goal(weighing("x", 1, "y", -1), 0));

        assertEquals(Map.of(), freed.coefs());
    }
}
