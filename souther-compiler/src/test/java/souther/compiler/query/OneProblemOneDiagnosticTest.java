package souther.compiler.query;

import souther.compiler.Compiler;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * One problem is one diagnostic, and it lands on the file that has it.
 *
 * <p>An answer is absent when something it read was absent, and several answers in a chain are
 * absent for the one reason. Whichever of them found it is where it is reported; the ones above it
 * say nothing, or the author is told the same thing once per question that could not be answered.
 */
class OneProblemOneDiagnosticTest {

    private static Map<String, List<Diagnostic>> diagnose(String id, String source) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put(id, source);
        return Compiler.diagnoseModules(byId, Set.of());
    }

    @Test
    void anImportOfAModuleThatIsNotThereIsReportedOnce() {
        List<Diagnostic> found = diagnose("a.sou", """
                module m.a
                import m.nope ( X )
                data A = { x: X }
                """).get("a.sou");

        assertEquals(1, found.size(), "one unknown import, one diagnostic: " + found);
        assertEquals("check.import.unknownmodule", found.get(0).messageKey());
    }

    @Test
    void aModuleInTheReservedNamespaceIsReportedOnce() {
        List<Diagnostic> found = diagnose("a.sou", """
                module souther.evil
                data A = Int
                """).get("a.sou");

        assertEquals(1, found.size(), "one reserved name, one diagnostic: " + found);
    }

    @Test
    void aSourceThatWillNotParseSaysSo() {
        List<Diagnostic> found = diagnose("bad.sou", """
                module app.bad
                data = = =
                """).get("bad.sou");

        assertEquals(1, found.size(),
                "the parse error belongs to the source it was found in: " + found);
    }
}
