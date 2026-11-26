package souther.compiler.examples;

import souther.compiler.core.Contract;
import souther.compiler.core.EnsuresEnforcement;
import souther.compiler.execute.DeclaredEnsures;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Which of the four placements of a clause leave a stand-in a check to run.
 *
 * <p>Asked of the loader the check is looked up in: one that refuses every lookup tells a stand-in
 * that runs a check from one that runs none, without a model. A crossing check is emitted by the
 * code that calls the stand-in, and a stand-in running one as well would hold the answer twice; a
 * callee check went with the body the stand-in replaced, and one another module's behavior is held
 * to is emitted by nothing that calls it.
 *
 * <p>This says which placements a stand-in runs a check for, and not how many checks a run makes:
 * that the crossing check is there is what {@code BodyGen} emits, read where it is emitted.
 */
class AStandInTakesOverOnlyTheCheckItsSubstitutionRemovesTest {

    private static final ValueName.Behavior HERE = new ValueName.Behavior("m", "convert");
    private static final ValueName.Behavior ELSEWHERE = new ValueName.Behavior("other", "convert");

    @Test
    void anAnswerTheCrossingChecksIsNotCheckedAgain() {
        assertDoesNotThrow(() -> checks(HERE,
                new EnsuresEnforcement.AtEachCrossing(contractOf(HERE))).holdAStandIn(
                        HERE, new Object[] {1L}, 2L));
    }

    @Test
    void anAnswerOfABehaviorStatingNothingIsNotChecked() {
        assertDoesNotThrow(() -> checks(HERE, EnsuresEnforcement.NoContract.INSTANCE)
                .holdAStandIn(HERE, new Object[] {1L}, 2L));
    }

    @Test
    void anAnswerTheReplacedBodyWouldHaveCheckedIsChecked() {
        assertThrows(LookedUp.class, () -> checks(HERE,
                new EnsuresEnforcement.AtTheCallee(contractOf(HERE))).holdAStandIn(
                        HERE, new Object[] {1L}, 2L));
    }

    @Test
    void anAnswerOfABehaviorAnotherModuleDeclaresIsChecked() {
        assertThrows(LookedUp.class, () -> checks(ELSEWHERE, null)
                .holdAStandIn(ELSEWHERE, new Object[] {1L}, 2L));
    }

    /**
     * The checks of module {@code m}, where {@code behavior} declares a clause and {@code m} placed
     * it as {@code placed} — or decided nothing about it, for {@code null}.
     */
    private static EnsuresChecks checks(ValueName.Behavior behavior, EnsuresEnforcement placed) {
        Map<ValueName.Behavior, EnsuresEnforcement> decided =
                placed == null ? Map.of() : Map.of(behavior, placed);
        return new EnsuresChecks(new RefusingEveryLookup(),
                new DeclaredEnsures("m", Map.of(behavior, contractOf(behavior)), decided),
                Set.of(behavior));
    }

    private static Contract contractOf(ValueName.Behavior behavior) {
        return new Contract(behavior,
                List.of(new Contract.Param(null, "a", Type.INT)), Type.INT, List.of());
    }

    /** That a check was looked up, which is a stand-in running one. */
    private static final class LookedUp extends RuntimeException {
        private static final long serialVersionUID = 1L;

        LookedUp(String name) {
            super(name);
        }
    }

    private static final class RefusingEveryLookup extends ClassLoader {

        RefusingEveryLookup() {
            super(null);
        }

        @Override
        protected Class<?> loadClass(String name, boolean resolve) {
            throw new LookedUp(name);
        }
    }
}
