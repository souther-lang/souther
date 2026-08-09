package souther.compiler.query;

import souther.compiler.diag.Located;
import souther.compiler.Compiler;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * One problem is one diagnostic, and it lands on the file that has it.
 *
 * <p>An answer is absent when something it read was absent, and several answers in a chain are
 * absent for the one reason. Whichever of them found it is where it is reported; the ones above it
 * say nothing, or the author is told the same thing once per question that could not be answered.
 */
class OneProblemOneDiagnosticTest {

    private static Map<String, List<Diagnostic>> diagnose(String source) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("a.sou", source);
        return Located.diagnosticsOf(Compiler.diagnoseModules(byId, Set.of()));
    }

    @Test
    void anImportOfAModuleThatIsNotThereIsReportedOnce() {
        List<Diagnostic> found = diagnose("""
                module m.a
                import m.nope ( X )
                data A = { x: X }
                """).get("a.sou");

        assertEquals(1, found.size(), "one unknown import, one diagnostic: " + found);
        assertEquals("module.unknown-module", found.get(0).messageKey());
    }

    @Test
    void aModuleInTheReservedNamespaceIsReportedOnce() {
        List<Diagnostic> found = diagnose("""
                module souther.evil
                data A = Int
                """).get("a.sou");

        assertEquals(1, found.size(), "one reserved name, one diagnostic: " + found);
    }

    /**
     * A helper is checked on its own and again wherever it is expanded, so a mistake in one is found
     * twice, at the same place, by two questions that cannot see each other. The author has one
     * mistake and is told once.
     */
    @Test
    void aMistakeInAHelperThatIsExpandedIntoABodyIsReportedOnce() {
        List<Diagnostic> found = diagnose("""
                module m.a

                data A = Int
                    invariant value >= 0

                let doubled (n: Int) : Int = n * "two"

                behavior twice : (a: A) -> A
                    constructs A
                let twice (a) = A(doubled(a.value))
                """).get("a.sou");

        assertEquals(1, found.size(),
                "one mistake in `doubled`, one diagnostic: " + found);
    }

    private static Map<String, List<Diagnostic>> diagnoseAs(String id, String source) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put(id, source);
        return Located.diagnosticsOf(Compiler.diagnoseModules(byId, Set.of()));
    }

    @Test
    void aSourceThatWillNotParseSaysSo() {
        List<Diagnostic> found = diagnoseAs("bad.sou", """
                module app.bad
                data = = =
                """).get("bad.sou");

        assertEquals(1, found.size(),
                "the parse error belongs to the source it was found in: " + found);
    }

    @Test
    void aNameDeclaredTwiceLeavesTheOtherNamesAlone() {
        List<Diagnostic> found = diagnose("""
                module m.a

                data A = Int

                data A = String

                data B = { a: A, n: Nowhere }
                """).get("a.sou");

        // The duplicate, and the name that denotes nothing. Not "unknown type A" as well: the first
        // A is still a declaration, so B's field still means something.
        assertEquals(2, found.size(), "the duplicate and the unknown name, and no more: " + found);
        assertTrue(found.stream().anyMatch(d -> "check.dup.data".equals(d.messageKey())));
        assertTrue(found.stream().anyMatch(d -> "check.unknown.type.msg".equals(d.messageKey())));
    }
}
