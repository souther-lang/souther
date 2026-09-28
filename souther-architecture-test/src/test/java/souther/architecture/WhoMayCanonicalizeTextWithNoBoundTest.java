package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.CodeModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeInstruction;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * In the run time, no text is canonicalized with no bound on the answer's length.
 *
 * <p>An operation that builds a string asks {@code Normalization.nfcWithin} for its answer, with
 * the length a {@code String} holds as the bound, so an answer past it is found before it is built
 * and aborts as the operation's contract says. The door text comes in by asks it the same way, and
 * refuses text whose canonical form has no place. {@code Normalization.nfc} asks for the answer
 * however long it is, so a caller of it is one whose answer can reach the host's own
 * {@code OutOfMemoryError} instead of the abort or the refusal.
 */
class WhoMayCanonicalizeTextWithNoBoundTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final String NORMALIZATION = "souther/unicode/Normalization";

    @Test
    void noRunTimeMethodCanonicalizesWithNoBound() {
        assertEquals(List.of(), canonicalizingWithNoBound(),
                "text is canonicalized within the length a String holds, so an answer past it"
                        + " aborts or is refused rather than exhausting the host");
    }

    private static List<String> canonicalizingWithNoBound() {
        Set<String> out = new TreeSet<>();
        for (ClassModel each : COMPILED.classesOf(COMPILED.module("souther-runtime"))) {
            for (MethodModel method : each.methods()) {
                for (CodeModel code : method.code().stream().toList()) {
                    for (CodeElement element : code) {
                        if (element instanceof InvokeInstruction invoke
                                && invoke.owner().asInternalName().equals(NORMALIZATION)
                                && invoke.name().stringValue().equals("nfc")) {
                            out.add(each.thisClass().asInternalName() + "#"
                                    + method.methodName().stringValue());
                        }
                    }
                }
            }
        }
        return new ArrayList<>(out);
    }
}
