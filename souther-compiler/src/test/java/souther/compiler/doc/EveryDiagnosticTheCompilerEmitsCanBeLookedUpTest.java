package souther.compiler.doc;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.DiagnosticCode;
import souther.compiler.diag.RetiredDiagnosticCode;

import java.io.IOException;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A code is what a diagnostic hands the reader to go and look the thing up with. Every code the
 * compiler prints therefore has to resolve, or the reader is handed a name and then told there is
 * nothing under it — which is worse than printing no code at all, since they spend the lookup
 * first.
 *
 * <p>What is checked is that the lookup answers, not that the codes and the sections are the same
 * set. Several diagnostics coming out of one language feature are explained together, and a section
 * carrying the codes of all of them is a section doing its job; what would be wrong is a code with
 * no way to reach the section that explains it.
 *
 * <p>The codes are {@link DiagnosticCode}'s constants, which is the whole domain rather than a
 * sample of it: a diagnostic is built through {@code Diagnostic.of(DiagnosticCode, key)} and there
 * is no other builder, so a code the compiler can print is one of these and nothing assembled at
 * run time can be another.
 */
class EveryDiagnosticTheCompilerEmitsCanBeLookedUpTest {

    @Test
    void everyCodeTheCompilerPrintsResolvesToASection() throws IOException {
        SpecDocument spec = SpecDocument.bundled();
        Set<String> unresolved = new TreeSet<>();
        for (DiagnosticCode code : DiagnosticCode.values()) {
            if (spec.section(code.docAnchor()) == null) {
                unresolved.add(code.name());
            }
        }
        for (RetiredDiagnosticCode code : RetiredDiagnosticCode.values()) {
            if (spec.section(code.docAnchor()) == null) {
                unresolved.add(code.name());
            }
        }

        assertFalse(DiagnosticCode.values().length == 0, "there are no diagnostic codes at all");
        assertEquals(Set.of(), unresolved,
                "the compiler prints these and `souther doc` has nothing to answer them with");
    }

}
