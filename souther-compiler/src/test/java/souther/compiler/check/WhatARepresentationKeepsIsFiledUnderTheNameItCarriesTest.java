package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.KeptCalls;
import souther.compiler.core.CompleteSignature;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A representation says which names it keeps standing, and each of them is the one its signature
 * carries.
 *
 * <p>What a signature is the signature of is on the signature. Filed under a name stated beside it,
 * the two could disagree — and then a call written to one operation is elaborated as another,
 * consistently, against the wrong declaration. No arity check catches that: the wrong declaration
 * is applied whole, so the call has the arguments it takes and answers what it answers.
 *
 * <p>So there is nothing to check here and nothing to state. What these say is that the name cannot
 * be stated: a representation is built out of signatures, and the filing is the signature's own
 * answer.
 */
class WhatARepresentationKeepsIsFiledUnderTheNameItCarriesTest {

    private static final ValueName.Stdlib.Operation LENGTH =
            ValueName.Stdlib.operation("List", "length");

    private static final ValueName.Stdlib.Operation REVERSE =
            ValueName.Stdlib.operation("List", "reverse");

    @Test
    void anOperationIsFoundUnderWhatItsSignatureNames() {
        Preserved keeping = Preserved.keeping(List.of(KeptCalls.signature(LENGTH)));

        assertEquals(KeptCalls.signature(LENGTH), keeping.signatureOf(LENGTH));
        assertNull(keeping.signatureOf(REVERSE), "nothing was said about it");
    }

    /** And the same for a value, which is recorded rather than filed. */
    @Test
    void aValueIsFoundUnderWhatItsSignatureNames() {
        ValueName half = new ValueName.Helper("demo", "half");
        Preserved.Settling settling = new Preserved.Settling();
        settling.settled(CompleteSignature.ofSettledValue(half, Type.INT));
        Preserved keeping = Preserved.valuesAlreadySettled(settling);

        assertEquals(half, keeping.valueKept(half).declaring().operation());
        assertNull(keeping.valueKept(new ValueName.Helper("demo", "other")));
    }

    /**
     * One operation kept under two signatures is refused rather than answered with the last.
     *
     * <p>Both would be signatures of that operation, so neither is wrong on its own and the call
     * gets whichever arrived last — which makes what a call means depend on the order a
     * representation was assembled in.
     */
    @Test
    void anOperationKeptTwiceIsRefused() {
        CompleteSignature declared = KeptCalls.signature(LENGTH);
        CompleteSignature narrower =
                CompleteSignature.ofDeclaration(LENGTH, List.of(Type.STRING), Type.INT);

        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> Preserved.keeping(List.of(declared, narrower)));

        assertTrue(e.getMessage().contains("List.length"), e.getMessage());
    }
}
