package souther.compiler;

import souther.compiler.diag.CompileException;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A behavior may not declare {@code constructs} for a type another module declares. Construction is
 * closed to the declaring module (ADR-0015), so the generated {@code __construct} is package-private
 * and the call fails with an {@code IllegalAccessError} at run time. The declaration is decidable
 * where it is written — the type's declaring module against the behavior's own — so it is rejected
 * there (issue #113).
 */
class CompileConstructsImportedTest {

    private static final String UP = """
            module up exposing ( Amount )
            data Amount = Int
            """;

    @Test
    void constructingAnImportedTypeIsRejected() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(UP, """
                        module down
                        import up ( Amount )

                        data Plan = { total: Amount }

                        behavior makePlan : (n: Int) -> Plan
                            constructs Plan, Amount
                        let makePlan (n) = Plan { total = Amount(n) }
                        """)));

        assertTrue(e.getMessage().contains("Amount"), e.getMessage());
        assertTrue(e.getMessage().contains("up"), "it names the module that declares it: " + e.getMessage());
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
        // reading across a module is what importing is for; only building across one is closed
        Compiler.compileModules(List.of(UP, """
                module down
                import up ( Amount )

                data Out = { doubled: Int }

                behavior twice : (a: Amount) -> Out
                    constructs Out
                let twice (a) = Out { doubled = a.value * 2 }
                """));
    }

    @Test
    void anInjectedBehaviorCannotConstructAnImportedTypeEither() {
        // the injected case has its own rule about exposure (E1305); this one is about ownership
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(UP, """
                        module down
                        import up ( Amount )

                        data Plan = { total: Amount }

                        behavior readPlan : (n: Int) -> Plan
                            constructs Plan, Amount
                        """)));

        assertTrue(e.getMessage().contains("Amount"), e.getMessage());
    }
}
