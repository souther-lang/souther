package souther.compiler.core;

import souther.compiler.abort.AbortKind;
import souther.compiler.abort.AbortSet;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@link EnsuresEnforcement#aborts}: a clause checked where the behavior answers or where its
 * answer crosses into the program may end a run without a value, and a behavior with no clause never
 * ends one for that reason.
 */
class AClauseCheckedAnywhereMayEndARunAndNoClauseNeverDoesTest {

    @Test
    void noContractAnswersNoneBecauseThereIsNoClauseToCheck() {
        AbortSet aborts = EnsuresEnforcement.NoContract.INSTANCE.aborts();

        assertTrue(aborts.isEmpty(), "a behavior with no clause never ends without a value for it");
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
