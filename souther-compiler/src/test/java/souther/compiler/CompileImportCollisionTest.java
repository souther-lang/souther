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
}
