package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;

import java.lang.reflect.RecordComponent;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A reason an evaluation answers nothing names the evaluation, and the decision a proof makes of
 * it says which copy it is in ({@link Core.InACopy}). A kind a reason names that cannot say is a
 * kind whose decisions the proof would put at the one place its body is written.
 *
 * <p>The population is the reasons' own components, so a reason added later that names a kind is
 * held to this without anybody adding it here. A component typed as any {@link Core} says nothing
 * of which kind it is and is asked of the tests that run each kind.
 */
class EveryKindANoCompletionProofNamesSaysTheCopyItIsInTest {

    @Test
    void everyKindAReasonNamesSaysItsCopy() {
        Set<String> silent = new TreeSet<>();
        Set<String> named = new TreeSet<>();
        for (Class<?> reason : Completion.NoCompletionProof.class.getPermittedSubclasses()) {
            for (RecordComponent component : reason.getRecordComponents()) {
                Class<?> type = component.getType();
                if (Core.class.isAssignableFrom(type) && type != Core.class) {
                    named.add(type.getSimpleName());
                    if (!Core.InACopy.class.isAssignableFrom(type)) {
                        silent.add(reason.getSimpleName() + "." + component.getName() + " : "
                                + type.getSimpleName());
                    }
                }
            }
        }
        assertFalse(named.isEmpty(), "the reasons name some kinds");
        assertEquals(Set.of(), silent,
                "a kind a reason names says which copy of its body it is in");
    }
}
