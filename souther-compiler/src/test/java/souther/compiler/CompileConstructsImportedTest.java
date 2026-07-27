package souther.compiler;

import souther.compiler.diag.CompileException;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A behavior constructs what its {@code constructs} names, wherever that type was declared
 * (ADR-0002). A type another module exposes may be built here, through the same checked entry every
 * construction takes — so the invariant runs, and what the declaration says is what happens.
 *
 * <p>A type a module keeps to itself stays unbuildable: its entry is not opened, and a value of it
 * can only be read.
 */
class CompileConstructsImportedTest {

    private static final String UP = """
            module up exposing ( Amount )
            data Amount = Int
                invariant value >= 0
            """;

    @Test
    void anExposedTypeOfAnotherModuleMayBeConstructedHere() {
        Compiler.compileModules(List.of(UP, """
                module down
                import up ( Amount )

                data Plan = { total: Amount }

                behavior makePlan : (n: Int) -> Plan
                    constructs Plan, Amount
                let makePlan (n) = Plan { total = Amount(n) }
                """));
    }

    @Test
    void anInjectedBehaviorMayConstructOneToo() {
        Compiler.compileModules(List.of(UP, """
                module down exposing ( Plan, readPlan )
                import up ( Amount )

                data Plan = { total: Amount }

                behavior readPlan : (n: Int) -> Plan
                    constructs Plan, Amount
                """));
    }

    @Test
    void constructingTheModulesOwnTypesIsFine() {
        Compiler.compileModules(List.of(UP, """
                module down
                import up ( Amount )

                data Plan = { total: Amount, note: Note }
                data Note = String

                behavior makePlan : (n: Int, a: Amount) -> Plan
                    constructs Plan, Note
                let makePlan (n, a) = Plan { total = a, note = Note("x") }
                """));
    }

    @Test
    void anImportedTypeMayStillBeReadAndPassedThrough() {
        Compiler.compileModules(List.of(UP, """
                module down
                import up ( Amount )

                data Out = { doubled: Int }

                behavior twice : (a: Amount) -> Out
                    constructs Out
                let twice (a) = Out { doubled = a.value * 2 }
                """));
    }

    /** The construction runs, and the invariant runs with it — at home or away. */
    @Test
    void theInvariantRunsOnAConstructionDeclaredInAnotherModule() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(
                Compiler.compileModules(List.of(UP, """
                        module down exposing ( Req, mint )
                        import up ( Amount )

                        data Req = { n: Int }

                        behavior mint : (r: Req) -> Amount constructs Amount
                        let mint (r) = Amount(r.n)
                        """)), getClass().getClassLoader());

        Object impl = loader.loadClass("down.Mint$Impl").getDeclaredConstructor().newInstance();
        Object ok = Codecs.apply(impl, Codecs.decoded(loader, "down.Req", Map.of("n", 5L)));
        assertEquals(5L, ok.getClass().getMethod("value").invoke(ok));

        Object bad = Codecs.decoded(loader, "down.Req", Map.of("n", -3L));
        souther.runtime.ConstraintViolation aborted = assertThrows(
                souther.runtime.ConstraintViolation.class, () -> Codecs.apply(impl, bad));
        assertTrue(aborted.getMessage().contains("Amount"), aborted.getMessage());
    }

    /** A constant argument is checked where it is written, whichever module declared the type: the
     * verdict a local newtype gets at compile time is the verdict an imported one gets. The
     * invariant here is one only the compile-time evaluation can decide — an interval invariant
     * would be settled earlier, by the discharge analysis, and say nothing about this path. */
    @Test
    void aConstantViolatingAnImportedInvariantIsACompileError() {
        String up = """
                module up exposing ( Email )
                import String ( contains )
                data Email = String
                    invariant contains("@", value)
                """;

        Compiler.compileModules(List.of(up, """
                module down
                import up ( Email )

                data Req = { n: Int }

                behavior mint : (r: Req) -> Email constructs Email
                let mint (r) = Email("a@b.com")
                """));

        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(up, """
                        module down
                        import up ( Email )

                        data Req = { n: Int }

                        behavior mint : (r: Req) -> Email constructs Email
                        let mint (r) = Email("nope")
                        """)));

        assertTrue(e.getMessage().contains("Email"), e.getMessage());
    }

    /** A type its module keeps to itself has no entry to build with. A value of it still arrives —
     * through a field of a data that module does expose — and reading it is all this module can do. */
    @Test
    void aTypeItsModuleKeepsToItselfCannotBeBuiltHere() {
        String hidden = """
                module hid exposing ( Invoice )
                data Amount = Int
                    invariant value >= 0
                data Invoice = { total: Amount }
                """;

        Compiler.compileModules(List.of(hidden, """
                module down
                data Out = { n: Int }

                behavior read : (i: hid.Invoice) -> Out constructs Out
                let read (i) = Out { n = i.total.value }
                """));

        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(hidden, """
                        module down
                        data Out = { n: Int }

                        behavior double : (i: hid.Invoice) -> Out constructs Out
                        let double (i) = {
                            let doubled = i.total + i.total
                            Out { n = doubled.value }
                        }
                        """)));

        assertTrue(e.getMessage().contains("Amount"), e.getMessage());
        assertTrue(e.getMessage().contains("expose"), e.getMessage());
    }
}
