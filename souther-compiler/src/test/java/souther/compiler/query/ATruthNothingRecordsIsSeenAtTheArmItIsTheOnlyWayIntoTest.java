package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.partition.DecisionReading;
import souther.compiler.partition.DecisionRule;
import souther.compiler.partition.ShownBy;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule through a truth no construct of the model answers is seen at the arm of the fork it is the
 * only way into.
 *
 * <p>A truth the body was handed — a position of the input, or a place inside what a dependency
 * answered — comes out a way at no comparison and no application, so nothing a run records says
 * which way it came out. The fork on it does: where the truth is the one way into an arm, a run down
 * the arm is a run that brought it out that way. Read without that, every rule through such a truth
 * was one no run could be placed at, and a body deciding on one was not measured at all.
 *
 * <p>Where it is one of several ways in, what else the run records says which. Under
 * {@code flag && n > 0} the {@code else} arm is entered by {@code flag} failing and by {@code flag}
 * holding while {@code n > 0} fails: a run that recorded {@code n > 0} ran it, which only a run past
 * {@code flag} does, and a run down the arm that never reached it stopped at {@code flag}.
 */
class ATruthNothingRecordsIsSeenAtTheArmItIsTheOnlyWayIntoTest {

    /** A truth of the input decided first, and a comparison under it. */
    private static final String A_POSITION = """
            module demo
            data A = { flag: Bool, n: Int }
            data Yes
            data No
            data Big
            behavior decides : (a: A) -> Yes | No | Big
            let decides (a) = if a.flag then Yes else if a.n > 100 then Big else No
            example decides
                | (A { flag = true, n = 1 }) -> Yes
                | (A { flag = false, n = 1 }) -> No
                | (A { flag = false, n = 101 }) -> Big
            """;

    /** A truth of a place inside what a dependency answered. */
    private static final String AN_ANSWER = """
            module demo
            data Reading = { ok: Bool, at: Int }
            data Yes
            data No
            behavior look : (at: Int) -> Reading
            behavior decides : (at: Int) -> Yes | No
                depends on look
            let decides (at, look) = if look(at).ok then Yes else No
            example decides
                | (1) with look = Reading { ok = true, at = 1 } -> Yes
                | (1) with look = Reading { ok = false, at = 1 } -> No
            """;

    /** A truth one of two ways into the arm a run takes when the condition fails. */
    private static final String BOTH = """
            module demo
            data Yes
            data No
            behavior decides : (flag: Bool, n: Int) -> Yes | No
            let decides (flag, n) = if flag && n > 0 then Yes else No
            example decides
                | (true, 1) -> Yes
                | (false, 1) -> No
                | (true, 0) -> No
            """;

    /** The same the other way round: one of two ways into the arm a run takes when it holds. */
    private static final String EITHER = """
            module demo
            data Yes
            data No
            behavior decides : (flag: Bool, n: Int) -> Yes | No
            let decides (flag, n) = if flag || n > 0 then Yes else No
            example decides
                | (true, 0) -> Yes
                | (false, 1) -> Yes
                | (false, 0) -> No
            """;

    /**
     * A truth settled short of the nearer of two operands, and a run down the arm that ran neither:
     * the one not reached first is what says how the truth came out.
     */
    private static final String TWO_DEEP = """
            module demo
            data Yes
            data No
            behavior decides : (flag: Bool, n: Int, m: Int) -> Yes | No
            let decides (flag, n, m) = if flag && n > 0 && m > 0 then Yes else No
            example decides
                | (true, 1, 1) -> Yes
                | (false, 1, 1) -> No
                | (true, 0, 1) -> No
                | (true, 1, 0) -> No
            """;

    /** The operator on the right of another, which runs it on every way into the {@code else}
     *  arm. */
    private static final String ON_THE_RIGHT = """
            module demo
            data Yes
            data No
            behavior decides : (flag: Bool, n: Int, m: Int) -> Yes | No
            let decides (flag, n, m) = if n > 0 || (flag && m > 0) then Yes else No
            example decides
                | (false, 1, 1) -> Yes
                | (true, 0, 1) -> Yes
                | (false, 0, 1) -> No
                | (true, 0, 0) -> No
            """;

    /** The right operand a name for a comparison worked out before the operator ran, which is
     *  recorded whichever way {@code flag} came out. */
    private static final String A_NAME_ON_THE_RIGHT = """
            module demo
            data Yes
            data No
            behavior decides : (flag: Bool, n: Int) -> Yes | No
            let decides (flag, n) = {
                let big = n > 0
                if flag && big then Yes else No
            }
            example decides
                | (true, 1) -> Yes
                | (false, 0) -> No
                | (true, 0) -> No
            """;

    @Test
    void eachRowIsPlacedAtTheRuleThroughATruthOfTheInput() {
        assertEveryRowIsPlacedAtItsOwnRule(A_POSITION, 3);
    }

    @Test
    void eachRowIsPlacedAtTheRuleThroughATruthADependencyAnswered() {
        assertEveryRowIsPlacedAtItsOwnRule(AN_ANSWER, 2);
    }

    @Test
    void eachRowIsPlacedAtTheRuleThroughATruthOneOfTwoWaysIntoAnArm() {
        assertEveryRowIsPlacedAtItsOwnRule(BOTH, 3);
        assertEveryRowIsPlacedAtItsOwnRule(EITHER, 3);
    }

    @Test
    void eachRowIsPlacedAtTheRuleThroughATruthSettledShortOfTheNearerOperand() {
        assertEveryRowIsPlacedAtItsOwnRule(TWO_DEEP, 4);
    }

    @Test
    void eachRowIsPlacedAtTheRuleThroughATruthAnOperatorOnTheRightRuns() {
        assertEveryRowIsPlacedAtItsOwnRule(ON_THE_RIGHT, 4);
    }

    /**
     * A comparison recorded before the operator ran is no sign of the left having gone on.
     *
     * <p>{@code n > 0} is worked out at the {@code let} and recorded for every run, so seeing it
     * says nothing of {@code flag}. Taken for the right having run, a run with {@code flag} failing
     * and {@code n > 0} failing would be placed at the rule where {@code flag} held.
     */
    @Test
    void aComparisonWorkedOutBeforeTheOperatorIsNotWhereTheLeftIsSeen() {
        for (DecisionReading.Ruled ruled : evidenceOf(A_NAME_ON_THE_RIGHT).read().found()) {
            ShownBy flag = ruled.shownBy().getFirst();
            assertFalse(flag instanceof ShownBy.AtAnOutcome,
                    () -> "`flag` is not seen where `n > 0` is: " + ruled.shownBy());
        }
    }

    private static void assertEveryRowIsPlacedAtItsOwnRule(String model, int ways) {
        DecisionEvidence evidence = evidenceOf(model);
        List<DecisionRule> rules = evidence.rules();
        assertEquals(ways, rules.size(), () -> "one rule per way through the body: " + rules);
        for (DecisionReading.Ruled ruled : evidence.read().found()) {
            assertTrue(ruled.shownBy().stream()
                            .noneMatch(shown -> shown instanceof ShownBy.NothingIsRecorded
                                    || shown instanceof ShownBy.ShortOf),
                    () -> "every condition of the rule is seen somewhere: " + ruled.shownBy());
        }
        DecisionEvidence.RowsPlaced placed = evidence.took().made()
                .orElseThrow(() -> new AssertionError("the rows were read: " + evidence.took()));
        assertEquals(ways, placed.rowsPlaced(), () -> "every row is placed at a rule: " + placed);
        assertEquals(Set.copyOf(rules), placed.rules(),
                () -> "and the rows are placed at every rule: " + placed);
    }

    private static DecisionEvidence evidenceOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation.db().ask(new Adequacy.Decides(compilation.modules().get(0))).value()
                .get("decides");
    }
}
