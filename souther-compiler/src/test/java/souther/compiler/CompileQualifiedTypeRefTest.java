package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.CompileException;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A type is reachable through the module that declares it. That is what lets one module use two
 * upstream modules that both declare {@code Amount} (issue #101): the collision has a way out
 * inside the module now, instead of forcing a rename upstream.
 */
class CompileQualifiedTypeRefTest {

    private static final String A = """
            module probe.a exposing ( Amount )
            data Amount = Int
            """;

    private static final String B = """
            module probe.b exposing ( Amount )
            data Amount = Decimal
            """;

    @Test
    void twoModulesDeclaringTheSameNameAreBothReachedQualified() {
        Map<String, byte[]> classes = Compiler.compileModules(List.of(A, B, """
                module probe.c exposing ( Line )
                data Line =
                    { counted: probe.a.Amount
                    , priced: probe.b.Amount
                    }
                """));

        assertTrue(classes.containsKey("probe.c.Line"), classes.keySet().toString());
        assertFalse(classes.containsKey("probe.c.Amount"), "no Amount is declared in probe.c");
    }

    @Test
    void aNewtypeWrapsAQualifiedType() {
        // the newtype's base is written like a type anywhere else, so it reaches through a module
        Map<String, byte[]> classes = Compiler.compileModules(List.of(A, """
                module probe.c exposing ( Counted )
                data Counted = probe.a.Amount
                """));

        assertTrue(classes.containsKey("probe.c.Counted"), classes.keySet().toString());
    }

    @Test
    void anImportedNameAndAQualifiedOneNameTheSameType() {
        Compiler.compileModules(List.of(A, """
                module probe.c
                import probe.a ( Amount )

                data Out = { n: Int }

                behavior read : (a: probe.a.Amount) -> Out constructs Out
                let read (a) = Out { n = a.value }

                behavior readBare : (a: Amount) -> Out constructs Out
                let readBare (a) = Out { n = a.value }
                """));
    }

    @Test
    void anAliasNamesTheModuleForThisModuleOnly() {
        Compiler.compileModules(List.of(A, B, """
                module probe.c exposing ( Line )
                import probe.a as Counting
                import probe.b as Pricing ( )

                data Line =
                    { counted: Counting.Amount
                    , priced: Pricing.Amount
                    }
                """));
    }

    @Test
    void aQualifiedReferenceNeedsNoImport() {
        Compiler.compileModules(List.of(A, """
                module probe.c exposing ( Line )
                data Line = { counted: probe.a.Amount }
                """));
    }

    @Test
    void aQualifierThatNamesNoModuleIsReported() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(A, """
                        module probe.c
                        data Line = { counted: probe.z.Amount }
                        """)));

        assertTrue(e.getMessage().contains("probe.z"), e.getMessage());
    }

    @Test
    void aTypeTheModuleDoesNotExposeIsReportedAsNotExposed() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of("""
                        module probe.hidden exposing ( Public )
                        data Public = Int
                        data Private = Int
                        """, """
                        module probe.c
                        data Line = { n: probe.hidden.Private }
                        """)));

        assertTrue(e.getMessage().contains("Private"), e.getMessage());
        assertTrue(e.getMessage().contains("exposed"), e.getMessage());
    }

    @Test
    void aNameTheModuleDoesNotDeclareIsReportedAsUndefined() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(A, """
                        module probe.c
                        data Line = { n: probe.a.Quantity }
                        """)));

        assertTrue(e.getMessage().contains("Quantity"), e.getMessage());
        assertTrue(e.getMessage().contains("probe.a"), e.getMessage());
    }

    /** An arm may name its case through the module that declares it. Without that, a module which
     * declares its own {@code Good} could not match an imported sum whose case is also {@code Good}:
     * the bare arm name would mean the local one. */
    @Test
    void aMatchArmMayNameItsCaseQualified() {
        Compiler.compileModules(List.of("""
                module probe.sum exposing ( Verdict, Good, Bad )
                data Good = { n: Int }
                data Bad = { why: String }
                data Verdict = Good | Bad
                """, """
                module probe.c exposing ( Out, read )
                data Good = { s: String }
                data Out = { n: Int }

                behavior read : (v: probe.sum.Verdict) -> Out constructs Out
                let read (v) =
                    match v with
                    | probe.sum.Good as g -> Out { n = g.n }
                    | probe.sum.Bad as b -> Out { n = 0 }
                """));
    }

    /** A dependency is a dependency however it is written: reaching another module by a qualified
     * name closes a cycle the same way an {@code import} does (E1501). */
    @Test
    void aCycleThroughQualifiedReferencesIsRejected() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of("""
                        module cyc.x exposing ( X )
                        data X = { y: cyc.y.Y? }
                        """, """
                        module cyc.y exposing ( Y )
                        data Y = { x: cyc.x.X? }
                        """)));

        assertTrue(e.getMessage().contains("E1501"), e.getMessage());
    }

    @Test
    void anAliasCannotTakeAQualifierThatIsAlreadyTaken() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(A, """
                        module probe.c
                        import probe.a as List

                        data Line = { n: Int }
                        """)));

        assertTrue(e.getMessage().contains("List"), e.getMessage());
    }

    @Test
    void twoImportsCannotShareAnAlias() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(A, B, """
                        module probe.c
                        import probe.a as M
                        import probe.b as M

                        data Line = { n: Int }
                        """)));

        assertTrue(e.getMessage().contains("M"), e.getMessage());
    }
}
