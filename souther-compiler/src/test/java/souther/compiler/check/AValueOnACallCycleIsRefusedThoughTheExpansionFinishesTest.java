package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.source.SourceId;

import souther.compiler.Compiler;
import souther.compiler.diag.msg.NameMessage;
import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Located;
import souther.compiler.frontend.CstFrontend;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value that reaches itself through a helper that terminates is still a value that reaches itself.
 *
 * <p>{@code depth} recurses on a strictly smaller part of its argument, so it terminates and the
 * totality check certifies it. It is therefore lowered to a method and its call is left standing
 * rather than expanded, which means the expansion of a body that reads {@code seed} finishes: the
 * substitution stops at the call. Evaluating {@code seed} does not stop —
 * {@code seed -> depth(...) -> seed} — because what {@code depth} answers where it bottoms out is
 * {@code seed} again.
 *
 * <p>So the two graphs are two graphs. What the expansion follows is which calls it keeps unfolding,
 * and what {@link ValueCycles} follows is what a value's definition rests on, which is every call it
 * reaches whether or not the expansion unfolds it. Narrowing the second to match the first would let
 * this module through, and nothing below would catch it: the emitted program is well typed and total
 * helper by helper, and only diverges when the value is asked for.
 */
class AValueOnACallCycleIsRefusedThoughTheExpansionFinishesTest {

    /** {@code seed} calls a total recursive helper whose base case reads {@code seed}. */
    private static final String CYCLE = """
            module demo

            data T = { c: T?, n: Int }
            data Out = Int

            behavior run : (t: T) -> Out
                constructs Out

            let seed = depth(T { c = None, n = 1 })

            let depth (t: T) : Int = match t.c with | Some x -> depth(x) | None -> seed

            let run (t) = Out(depth(t))
            """;

    /** The same module with the base case answering a number, so nothing reaches back to the value. */
    private static final String WELL_FOUNDED = CYCLE.replace("| None -> seed", "| None -> t.n");

    private static List<Diagnostic> diagnose(String source) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("a.sou", source);
        return Located.diagnosticsOf(Compiler.diagnoseModules(byId, Set.of())).get(new SourceId("a.sou"));
    }

    @Test
    void theValueIsRefused() {
        List<Diagnostic> found = diagnose(CYCLE);

        assertEquals(1, found.size(), "one mistake, one report: " + found);
        assertInstanceOf(NameMessage.AValueReachesItself.class, found.get(0).said());
    }

    /** And the helper it goes round is not what is wrong with it: on its own it compiles. */
    @Test
    void theSameHelperWithoutTheValueOnItIsFine() {
        assertEquals(List.of(), diagnose(WELL_FOUNDED));
    }

    /**
     * The refusal is not the expansion running out of room. Handed the module the check refuses, the
     * expansion finishes — the call to the recursive helper is left standing, so the substitution
     * has an end.
     */
    @Test
    void theExpansionOfThatModuleFinishes() {
        Ast.Module parsed = CstFrontend.parse(CYCLE);
        HelperInliner inliner = HelperInliner.forModule(Resolve.module(parsed, SyntaxSymbols.of(parsed, DefaultStdlib.get())), DefaultStdlib.get());

        Hir.Expr expanded = assertDoesNotThrow(() -> inliner.inline(
                inliner.held().get(new souther.compiler.ast.DefinitionName("depth"))
                        .definition().writtenBody(), inliner.bodyOf("depth")));

        assertTrue(expanded != null, "a body the expansion finished with");
    }
}
