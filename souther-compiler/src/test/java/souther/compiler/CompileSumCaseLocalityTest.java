package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A declared sum lists cases its own module declares. The generated sum is a sealed interface, and
 * only its own package can implement it (ADR-0057), so a case from another module would be named in
 * {@code permits} without implementing it — a hierarchy no value satisfies and no exhaustive switch
 * has an arm for. Reported where the sum is written.
 */
class CompileSumCaseLocalityTest {

    private static final String UP = """
            module up exposing ( Cash, Card )

            data Cash
            data Card
            """;

    private static CompileException rejected(String down) {
        return assertThrows(CompileException.class, () -> Compiler.compileModules(List.of(UP, down)));
    }

    @Test
    void anImportedCaseIsNotACaseOfThisModulesSum() {
        CompileException e = rejected("""
                module d exposing ( Pay )
                import up ( Cash, Card )

                data Pay = Cash | Card
                """);

        assertTrue(e.getMessage().contains("Cash"), e.getMessage());
        assertTrue(e.getMessage().contains("up"), e.getMessage());
    }

    @Test
    void aSumOfItsOwnModulesCasesIsFine() {
        Compiler.compileModules(List.of(UP, """
                module d exposing ( Pay )

                data Yen
                data Points
                data Pay = Yen | Points
                """));
    }
}
