package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.HelperEntry;
import souther.compiler.check.HelperTable;
import souther.compiler.check.InliningPolicy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.ReachName;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The library's part of what declarations answer out of and of who decides at their forks is read
 * once and stood beside each module's, and comes to what reading everything together comes to.
 *
 * <p>The oracles are the reading it replaces. What a module's declarations answer out of, read with
 * the library held where it was read on its own, is the one fixed point over all of them; and the
 * forks read with the library kept are the forks read with nothing kept. A model whose helper hands
 * a closure to a library operation, and whose behavior forks on what that helper answers, has the
 * module's part rest on the library's.
 */
class TheLibrarysPartOfADecisionReadingIsReadOnceTest {

    private static final String MODEL = """
            module demo

            let kept (xs: List<Int>, n: Int): List<Int> = List.filter(x -> x > n, xs)

            behavior pick : (xs: List<Int>, n: Int) -> Int
            let pick (xs, n) =
                if List.length(kept(xs, n)) >= 2 then 1 else 0
            """;

    private static HelperTable table() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList(),
                "the model under test compiles");
        return compilation.db().ask(new Bodies.Expanding("demo", InliningPolicy.FULL)).value()
                .table();
    }

    @Test
    void whatTheModuleAnswersOutOfIsTheFixedPointOverEverything() {
        HelperTable table = table();
        Map<ReachName.Declaration, Hir.FnDef> library = new LinkedHashMap<>();
        Map<ReachName.Declaration, Hir.FnDef> module = new LinkedHashMap<>();
        Map<ReachName.Declaration, Hir.FnDef> all = new LinkedHashMap<>();
        table.reachable().forEach((reference, entry) -> {
            (reference instanceof ReachName.OfLibrary ? library : module)
                    .put(reference, entry.definition());
            all.put(reference, entry.definition());
        });
        assertFalse(library.isEmpty(), "the table reaches the library");
        assertFalse(module.isEmpty(), "and the module's own helper");

        assertEquals(AnswerDependencies.of(all),
                AnswerDependencies.of(module, AnswerDependencies.of(library)));
    }

    /**
     * Handed as the declarations of one reading, nothing is told apart as the library's: every one
     * of them is read together, which is the reading this stands in for.
     */
    @Test
    void theForksReadWithTheLibraryKeptAreTheForksReadAllTogether() {
        HelperTable table = table();
        Map<ReachName.Declaration, HelperEntry> reachable = table.reachable();
        Map<ReachName.Declaration, Hir.FnDef> together = new LinkedHashMap<>();
        reachable.forEach((reference, entry) -> together.put(reference, entry.definition()));

        DecisionSources oracle = DecisionSources.of(null, Map.of(), together);
        DecisionSources kept = DecisionSources.of(table.library(), reachable, Map.of());
        DecisionSources again = DecisionSources.of(table.library(), reachable, Map.of());

        assertTrue(oracle.byFork().size() > 1, "the library and the module write forks");
        assertEquals(oracle, kept);
        assertEquals(oracle, again, "and read from what was kept");
    }
}
