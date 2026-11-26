package souther.compiler.examples;

import souther.compiler.core.Contract;
import souther.compiler.core.EnsuresEnforcement;
import souther.compiler.execute.DeclaredEnsures;
import souther.compiler.generated.GeneratedLinkage.GeneratedClassDefect;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Which of the ways a module holds its behavior's clause leave a stand-in for the behavior a check
 * to run.
 *
 * <p>Asked of the loader the check is looked up in: one that refuses every lookup tells a stand-in
 * that runs a check from one that runs none, without a model. A body checks its own answer, so a
 * stand-in taking its place runs that check. What Java supplies is checked by the code calling it,
 * so a stand-in running the check as well would hold the answer twice.
 *
 * <p>The answer is the declaring module's: a stand-in is called from more than one module's code,
 * and what it owes cannot turn on which.
 */
class AStandInTakesOverOnlyTheCheckItsSubstitutionRemovesTest {

    private static final ValueName.Behavior CONVERT = new ValueName.Behavior("lib", "convert");

    @Test
    void anAnswerTheReplacedBodyWouldHaveCheckedIsChecked() {
        assertThrows(LookedUp.class, () -> checks(new EnsuresEnforcement.AtTheCallee(contract()))
                .holdAStandIn(CONVERT, new Object[] {1L}, 2L));
    }

    @Test
    void anAnswerTheCallingCodeChecksIsNotCheckedAgain() {
        assertDoesNotThrow(() -> checks(new EnsuresEnforcement.AtEachCrossing(contract()))
                .holdAStandIn(CONVERT, new Object[] {1L}, 2L));
    }

    @Test
    void anAnswerOfABehaviorStatingNothingIsNotChecked() {
        assertDoesNotThrow(() -> checks(EnsuresEnforcement.NoContract.INSTANCE)
                .holdAStandIn(CONVERT, new Object[] {1L}, 2L));
    }

    /** A behavior this reading was not given is this compiler failing, not a behavior that states
     *  nothing. */
    @Test
    void aStandInForABehaviorNothingReadIsThisCompilerFailing() {
        assertThrows(GeneratedClassDefect.class, () -> checks(EnsuresEnforcement.NoContract.INSTANCE)
                .holdAStandIn(new ValueName.Behavior("lib", "unread"), new Object[] {1L}, 2L));
    }

    /** The checks where the module declaring {@code convert} holds its clause as {@code held}. */
    private static EnsuresChecks checks(EnsuresEnforcement held) {
        return new EnsuresChecks(new RefusingEveryLookup(), new DeclaredEnsures(Map.of(CONVERT, held)));
    }

    private static Contract contract() {
        return new Contract(CONVERT,
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
