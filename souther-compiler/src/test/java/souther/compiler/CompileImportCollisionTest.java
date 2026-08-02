package souther.compiler;

import souther.compiler.diag.CompileException;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A name that arrives twice says so. Two bounded contexts each exposing {@code Amount} are ordinary,
 * and the module integrating both used to be told the import "conflicts with a local definition" —
 * one it had never written (issue #101). The two cases are told apart, and the import collision names
 * both modules it came from.
 */
class CompileImportCollisionTest {

    private static final String A = """
            module probe.a
            exposing ( Amount )
            data Amount = Int
            """;

    private static final String B = """
            module probe.b
            exposing ( Amount )
            data Amount = Decimal
            """;

    @Test
    void twoImportsOfTheSameNameReportBothModules() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(A, B, """
                        module probe.c
                        import probe.a ( Amount )
                        import probe.b ( Amount )
                        data Line = { a: Amount }
                        """)));

        assertTrue(e.getMessage().contains("probe.a"), e.getMessage());
        assertTrue(e.getMessage().contains("probe.b"), e.getMessage());
        assertFalse(e.getMessage().contains("local definition"),
                "there is no local definition to conflict with: " + e.getMessage());
    }

    @Test
    void theCollisionPointsAtBothImports() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(A, B, """
                        module probe.c
                        import probe.a ( Amount )
                        import probe.b ( Amount )
                        data Line = { a: Amount }
                        """)));

        assertEquals(3, e.diagnostic().region().start().line(), "the caret is on the second import");
        assertEquals(1, e.diagnostic().secondary().size(), "the first import is labelled too");
        assertEquals(2, e.diagnostic().secondary().get(0).region().start().line());
    }

    @Test
    void aCollisionWithARealLocalDefinitionStillSaysSo() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(A, """
                        module probe.c
                        import probe.a ( Amount )
                        data Amount = String
                        data Line = { a: Amount }
                        """)));

        assertTrue(e.getMessage().contains("local"), e.getMessage());
        assertTrue(e.getMessage().contains("Amount"), e.getMessage());
    }

    @Test
    void theSameNameTwiceFromOneModuleIsReportedAsThat() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(A, """
                        module probe.c
                        import probe.a ( Amount )
                        import probe.a ( Amount )
                        data Line = { a: Amount }
                        """)));

        assertTrue(e.getMessage().contains("probe.a"), e.getMessage());
        assertFalse(e.getMessage().contains("local definition"), e.getMessage());
    }

    @Test
    void distinctImportedNamesAreFine() {
        Compiler.compileModules(List.of(A, B, """
                module probe.c
                import probe.a ( Amount )
                data Line = { a: Amount }
                """));
    }

    /**
     * Which kind of declaration the import lands beside does not enter into it. A data, a
     * {@code let} and a behavior all reach the value namespace under the name they are written
     * with, so any of them beside an import of that name is one spelling with two answers. The
     * check was written for a data and stopped there: a behavior of the same spelling compiled and
     * emitted a call to the imported one, which is a class that has no such method (issue #287).
     */
    @Test
    void anImportBesideADeclarationOfAnyKindIsRefused() {
        String up = """
                module up exposing ( twice, Thing )
                data Thing = { a: Int }
                behavior twice : (n: Int) -> Int
                let twice (n) = n * 2
                """;
        String upValue = """
                module up exposing ( twice )
                let twice (n: Int) = n * 2
                """;

        assertEquals("check.import.conflict", refused(List.of(up, """
                module probe.c
                import up ( twice )
                behavior twice : (a: Int, b: Int) -> Int
                let twice (a, b) = a * b
                data Line = { a: Int }
                """)));
        assertEquals("check.import.conflict", refused(List.of(upValue, """
                module probe.c
                import up ( twice )
                let twice (a: Int, b: Int) = a * b
                data Line = { a: Int }
                """)));
        assertEquals("check.import.conflict", refused(List.of(up, """
                module probe.c
                import up ( Thing )
                let Thing (n: Int) = n
                data Line = { a: Int }
                """)));
    }

    /** The standard library is imported by the same rule. A module's own declaration used to shadow
     * the import instead, so one spelling meant the library's function on one line and the module's
     * own definition on the next. */
    @Test
    void aLibraryImportBesideADeclarationIsRefused() {
        assertEquals("check.import.conflict", refused(List.of("""
                module probe.c
                import List ( map )
                let map (n: Int) = n + 1
                data Line = { a: Int }
                """)));
    }

    /** A binding is not a declaration. It is written inside a body, and an import says what a name
     * means where no binding answers it. */
    @Test
    void aBindingSpelledLikeAnImportIsStillTheBinding() {
        Compiler.compileModules(List.of("""
                module probe.c
                import List ( map )
                data In = { xs: List<Int> }
                data Out = { n: Int }
                behavior go : (i: In) -> Out constructs Out
                let go (i) = {
                    let map = 7
                    Out { n = map }
                }
                """));
    }

    private static String refused(List<String> modules) {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(modules));
        return e.diagnostic().messageKey();
    }
}
