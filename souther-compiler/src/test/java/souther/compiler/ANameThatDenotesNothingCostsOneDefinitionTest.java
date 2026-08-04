package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Located;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A name that denotes nothing costs the definition it was written in, and nothing else (issue #335).
 *
 * <p>The compiler abandons such a definition rather than reporting it twice, which is what
 * {@code Unanswerable} says. That signal belongs to the check: it is raised where a body is read for
 * meaning and caught where one definition's check ends. A reading done for a different reason — the
 * best-effort settling of a helper's unwritten parameter types, which runs before the check and
 * reports nothing — must answer "no type" instead of letting the signal past, because there is no
 * check boundary above it to catch it. Left alone it reached the author as a bare stack trace, and
 * took the language server's answer for the file with it.
 *
 * <p>The settling asks {@code HelperParams.determine} for the types a body gives, and so does the
 * check. They want opposite things of the signal, which is why it is answered at the settling's call
 * and not inside the reading the two of them share: suppressed inside, a helper whose body rests on
 * a broken name would be reported as a parameter the author must annotate, which is that one mistake
 * seen from another angle rather than anything new to fix.
 */
class ANameThatDenotesNothingCostsOneDefinitionTest {

    /** The reduced case from the issue: the name stands in an arm beside the parameter's own use. */
    private static final String IN_AN_ARM = """
            module demo
            let f (a) = if a == 1 then a else Nope
            """;

    /** The shape the specification itself is written in, which is where this was found. */
    private static final String AS_THE_SPEC_WRITES_IT = """
            module demo
            let preApprove (request, approverId) = {
                guard approverId == request.applicant.managerId
                    else NotAuthorized

                PreApproved { ...request, preApprovedAt = now(), preApprover = approverId }
            }
            """;

    private static List<Located> diagnosed(String source) {
        return Compiler.diagnoseModules(Map.of("demo", source)).getOrDefault("demo", List.of());
    }

    private static List<String> messageKeys(String source) {
        return diagnosed(source).stream().map(l -> l.diagnostic().messageKey()).toList();
    }

    @Test
    void everyEntryPointAnswersWithTheNameRatherThanTheAbandonSignal() {
        // The signal carries no diagnostic and no frames, so a caller that meets it has nothing to
        // render and nothing to read. Each of these is someone's only way in.
        for (String source : List.of(IN_AN_ARM, AS_THE_SPEC_WRITES_IT)) {
            assertThrows(CompileException.class, () -> Compiler.compile(source),
                    "`compile` rejects it as the unknown name it is");
            assertThrows(CompileException.class, () -> Compiler.compileWithWarnings(source),
                    "`compileWithWarnings` rejects it as the unknown name it is");
            assertThrows(CompileException.class, () -> Compiler.compiled(source, "demo"),
                    "`compiled` rejects it as the unknown name it is");
        }
    }

    @Test
    void theLanguageServerIsAnsweredWithDiagnosticsForAFileBeingTyped() {
        // `diagnoseModules` is the server's path. A throw here is not a diagnostic it can show, and
        // it takes the dispatch loop with it.
        assertEquals(List.of("check.unknown.name.msg"), messageKeys(IN_AN_ARM),
                "the file being typed answers with the name that denotes nothing");
        assertTrue(messageKeys(AS_THE_SPEC_WRITES_IT).contains("check.unknown.name.msg"),
                "and so does the shape the specification is written in");
    }

    @Test
    void theNameIsSaidOnceAndNothingIsAskedOfTheParameterBesideIt() {
        // Everything that follows from the broken name is that one mistake seen from another angle.
        // Telling the author to annotate `a` as well sends them at a parameter that is not the
        // problem: fixing `Nope` is what settles it.
        assertEquals(List.of("check.unknown.name.msg"), messageKeys(IN_AN_ARM),
                "the parameter beside the name is not reported as undetermined");
    }

    @Test
    void everyOtherDefinitionInTheModuleIsStillChecked() {
        // The point of abandoning one definition: an author fixing one name is still told the rest.
        assertEquals(List.of("check.unknown.name.msg", "check.unknown.name.msg"), messageKeys("""
                module demo
                let f (a) = if a == 1 then a else Nope
                let h (b) = b + Missing
                """), "both names are reported, one per definition");
    }

    @Test
    void aParameterTheBodyGenuinelyLeavesOpenIsStillReported() {
        // The signal is answered where it is raised for a broken name, not suppressed wholesale: a
        // body that names no type for its parameter is a different thing, and still says so.
        assertEquals(List.of("check.helper.infer"), messageKeys("""
                module demo
                let id (v) = v
                """), "nothing in the body names a type for `v`, so the annotation is asked for");
        assertEquals(List.of("check.helper.infer.field"), messageKeys("""
                module demo
                let g (r) = r.x
                """), "a parameter only ever read through a field still says which it was");
    }
}
