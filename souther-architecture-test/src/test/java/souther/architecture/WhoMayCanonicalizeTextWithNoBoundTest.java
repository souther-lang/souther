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
 * In the run time, text is canonicalized with no bound on the answer's length only where it
 * arrives from outside.
 *
 * <p>An operation that builds a string asks {@code Normalization.nfcWithin} for its answer, with
 * the length a {@code String} holds as the bound, so an answer past it is found before it is built
 * and aborts as the operation's contract says. {@code Normalization.nfc} asks for the answer
 * however long it is. A builder calling it is one whose answer can reach the host's own
 * {@code OutOfMemoryError} instead of the abort. The one place it is still called is the door text
 * comes in by, where what an over-long canonical form is refused as is the door's to say.
 */
class WhoMayCanonicalizeTextWithNoBoundTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final String NORMALIZATION = "souther/unicode/Normalization";

    private static final List<String> CANONICALIZES_WITH_NO_BOUND = List.of(
            "souther/runtime/Strings#admitted");

    @Test
    void everyRunTimeMethodThatCanonicalizesWithNoBoundIsWrittenDownHere() {
        assertEquals(CANONICALIZES_WITH_NO_BOUND, canonicalizingWithNoBound(),
                "a string an operation builds is canonicalized within the length a String holds,"
                        + " so an answer past it aborts rather than exhausting the host");
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
