package souther.compiler.core;

import souther.compiler.abort.AbortKind;
import souther.compiler.abort.AbortSet;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@link EnsuresEnforcement#aborts} on the two enforcement states that carry no {@link Contract} —
 * {@link EnsuresEnforcement.NoContract} and {@link EnsuresEnforcement.NotDecidedHere} — which
 * {@link EnsuresEnforcement#contract} both answer {@code null} for, and which {@code aborts()} must
 * not answer alike: a behavior with no clause never aborts for that reason, but a behavior this
 * compilation has not classified is a question with no answer yet, not a considered "never".
 */
class NotDecidedHereRefusesToAnswerWhetherItAbortsTest {

    @Test
    void noContractAnswersNoneBecauseThereIsNoClauseToCheck() {
        AbortSet aborts = EnsuresEnforcement.NoContract.INSTANCE.aborts();

        assertTrue(aborts.isEmpty(), "a behavior with no clause never ends without a value for it");
    }

    @Test
    void notDecidedHereRefusesRatherThanAnsweringNone() {
        assertThrows(IllegalStateException.class,
                EnsuresEnforcement.NotDecidedHere.INSTANCE::aborts,
                "this compilation has not decided whether the crossing checks anything, which is"
                        + " not the same fact as AbortSet.NONE");
    }

    @Test
    void aCheckedClauseAnswersEnsuresNotHeldWhicheverSideChecksIt() {
        Contract contract = new Contract(
                new ValueName.Behavior("demo", "f"), List.of(), Type.INT, List.of());

        assertEquals(AbortSet.of(AbortKind.ENSURES_NOT_HELD),
                new EnsuresEnforcement.AtTheCallee(contract).aborts());
        assertEquals(AbortSet.of(AbortKind.ENSURES_NOT_HELD),
                new EnsuresEnforcement.AtEachCrossing(contract).aborts());
    }
}
