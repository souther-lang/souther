package souther.compiler.core;

import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import java.util.EnumMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A snapshot of what the language declares of its kernels answers for every one of them.
 *
 * <p>Everything downstream reads it that way: a program hands it to whoever emits from it, and an
 * emitter asks with a kernel and uses what comes back without asking whether anything did. That
 * holds because a snapshot with a hole in it cannot be made — which is a thing to say here rather
 * than a thing for each reader to check, and a thing to hold rather than to write down.
 */
class ASnapshotOfWhatTheLanguageDeclaresIsWholeTest {

    @Test
    void aSnapshotAnswersForEveryKernelTheLanguageHas() {
        KernelSignatures snapshot = KernelSignatures.of(declaringEvery());

        for (Kernel kernel : Kernel.values()) {
            assertNotNull(snapshot.signatureOf(kernel), kernel::key);
        }
    }

    @Test
    void andOneMissingAKernelIsRefusedWhereItIsMade() {
        Map<Kernel, KernelSignature> without = declaringEvery();
        without.remove(Kernel.DECIMAL_ROUND);

        assertEquals("this compiler names the kernel(s) [decimal.round], which the standard library"
                        + " declares nothing for",
                assertThrows(IllegalArgumentException.class, () -> KernelSignatures.of(without))
                        .getMessage());
    }

    /**
     * And so is one holding a kernel and no signature for it.
     *
     * <p>The half a reading of the keys cannot see. A map answers for a key it holds a null under,
     * so a snapshot checked by comparing key sets would be whole by that reading and would answer
     * null to the reader that asked — which is the absence this exists to keep out, arriving
     * somewhere far from the omission that made it.
     */
    @Test
    void andSoIsOneHoldingAKernelWithNoSignature() {
        Map<Kernel, KernelSignature> emptyHanded = declaringEvery();
        emptyHanded.put(Kernel.DECIMAL_ROUND, null);

        assertEquals("this compiler names the kernel(s) [decimal.round], which the standard library"
                        + " declares nothing for",
                assertThrows(IllegalArgumentException.class, () -> KernelSignatures.of(emptyHanded))
                        .getMessage());
    }

    /** A signature for every kernel. What each says is nothing to do with this: what is being held
     *  is that a snapshot answers for all of them, not what any one of them answers. */
    private static Map<Kernel, KernelSignature> declaringEvery() {
        Map<Kernel, KernelSignature> declared = new EnumMap<>(Kernel.class);
        for (Kernel kernel : Kernel.values()) {
            declared.put(kernel, new KernelSignature(List.of(), Type.INT));
        }
        return declared;
    }
}
