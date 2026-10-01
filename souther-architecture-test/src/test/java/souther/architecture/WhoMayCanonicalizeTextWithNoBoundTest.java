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
 * In the run time, no text is canonicalized or case-mapped with no bound on the answer's length.
 *
 * <p>An operation that builds a string asks the shared text rules for its answer within the length
 * a {@code String} holds ({@code Normalization.normalizeWithin}, {@code CaseConversion.lowercaseWithin}
 * and {@code uppercaseWithin}), so an answer past it is found before it is built and aborts as the
 * operation's contract says. The door text comes in by asks it the same way, and refuses text whose
 * canonical form has no place. The same rules without a bound answer however long the answer is,
 * so a caller of one is one whose answer can reach the host's own {@code OutOfMemoryError} instead
 * of the abort or the refusal.
 */
class WhoMayCanonicalizeTextWithNoBoundTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final String NORMALIZATION = "net/unit8/notation199x/Normalization";

    private static final String CASE_CONVERSION = "net/unit8/notation199x/CaseConversion";

    /** Each way of asking for an answer with no bound, as {@code owner#name}. */
    private static final Set<String> UNBOUNDED = Set.of(
            NORMALIZATION + "#nfc",
            NORMALIZATION + "#normalize",
            CASE_CONVERSION + "#lowercase",
            CASE_CONVERSION + "#uppercase");

    /** Each way of asking for it within a bound. */
    private static final Set<String> BOUNDED = Set.of(
            NORMALIZATION + "#normalizeWithin",
            CASE_CONVERSION + "#lowercaseWithin",
            CASE_CONVERSION + "#uppercaseWithin");

    @Test
    void noRunTimeMethodCanonicalizesWithNoBound() {
        assertEquals(List.of(), asking(UNBOUNDED),
                "text is canonicalized within the length a String holds, so an answer past it"
                        + " aborts or is refused rather than exhausting the host");
    }

    /**
     * And the walk sees the run time ask for an answer within a bound, each way it does, so an
     * empty answer above is about callers that are there to be seen.
     */
    @Test
    void theWalkFindsEveryBoundedAsk() {
        Set<String> asked = new TreeSet<>();
        for (String caller : asking(BOUNDED)) {
            asked.add(caller.substring(caller.indexOf(' ') + 1));
        }
        assertEquals(new TreeSet<>(BOUNDED), asked);
    }

    /** Each run-time method that calls one of {@code callees}, as {@code caller callee}. */
    private static List<String> asking(Set<String> callees) {
        Set<String> out = new TreeSet<>();
        for (ClassModel each : COMPILED.classesOf(COMPILED.module("souther-runtime"))) {
            for (MethodModel method : each.methods()) {
                for (CodeModel code : method.code().stream().toList()) {
                    for (CodeElement element : code) {
                        if (element instanceof InvokeInstruction invoke) {
                            String callee = invoke.owner().asInternalName() + "#"
                                    + invoke.name().stringValue();
                            if (callees.contains(callee)) {
                                out.add(each.thisClass().asInternalName() + "#"
                                        + method.methodName().stringValue() + " " + callee);
                            }
                        }
                    }
                }
            }
        }
        return new ArrayList<>(out);
    }
}
