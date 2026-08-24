package souther.compiler.check;

import souther.compiler.stdlib.Stdlib;
import souther.compiler.Compiler;
import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.frontend.CstFrontend;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Expanding a recursive helper's own body narrows what its parameters reach, and narrows nothing else.
 *
 * <p>A recursive helper is lowered to a method, and its body is expanded with its own parameters in
 * force. A parameter sharing a declaration's name — {@code List.foldFrom}'s function parameter
 * {@code step}, in a module that also declares {@code let step} — is a parameter application there and
 * not a call to that declaration.
 *
 * <p>Stated on the table rather than only through a compile, because getting it wrong does not fail:
 * a table that hid nothing would expand the declaration where the parameter is applied and keep
 * expanding, and what the author would see is the compile not finishing. A run that never comes back
 * is not a red test.
 */
class AParameterHidesTheDeclarationItIsNamedLikeTest {

    /** A module that declares a helper named like {@code foldFrom}'s function parameter, and folds. */
    private static final String DECLARES_STEP = """
            module demo

            data In = { ns: List<Int> }
            data Out = { n: Int }

            let step (n: Int) : Int = n + 1

            behavior go : (i: In) -> Out
                constructs Out
            let go (i) = Out { n = List.fold((acc, x) -> acc + step(x), 0, i.ns) }
            """;

    private static HelperTable tableOf(String source) {
        Ast.Module parsed = CstFrontend.parse(source);
        Hir.Module resolved = Resolve.module(parsed, SyntaxSymbols.of(parsed, souther.compiler.DefaultStdlib.get()));
        return HelperTable.of(resolved, Map.of(), InliningPolicy.FULL, souther.compiler.DefaultStdlib.get());
    }

    @Test
    void aHiddenNameReachesNothingAndTheOthersAreUntouched() {
        HelperTable table = tableOf(DECLARES_STEP);

        assertNotNull(table.reached("step"), "the module declares it");
        assertNotNull(table.reached("List.foldFrom"), "and the library declares this");

        HelperTable inside = table.hiding(List.of("step"));

        assertNull(inside.reached("step"), "a parameter named like it hides it");
        assertNotNull(inside.reached("List.foldFrom"), "and hides nothing else");
        assertNotNull(table.reached("step"), "the table it was taken from is unchanged");
    }

    @Test
    void hidingANameNothingReachesChangesNothing() {
        HelperTable table = tableOf(DECLARES_STEP);

        assertTrue(table.hiding(List.of("nobodyWroteThis")) == table,
                "a table narrowed by nothing is the table it was");
    }

    /** What the narrowing is for: the module above compiles, rather than expanding the declaration
     * where the fold applies its parameter and never stopping. */
    @Test
    void aModuleDeclaringAHelperNamedLikeAFoldsParameterCompiles() {
        assertFalse(Compiler.compile(DECLARES_STEP).isEmpty());
    }
}
