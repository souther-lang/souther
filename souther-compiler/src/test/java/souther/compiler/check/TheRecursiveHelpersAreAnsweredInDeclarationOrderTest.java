package souther.compiler.check;

import souther.compiler.stdlib.Stdlib;
import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.frontend.CstFrontend;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The recursive helpers are answered in the order they were declared.
 *
 * <p>Every member of a mutual cycle recurses, so a check with something to say about one of them has
 * it to say about all: {@code HelperTyping} reports the first that declares no return type, and
 * {@code TotalityChecker} walks them in the same order. Which one a reader reaches first is what a
 * compile says, so the whole sequence is pinned here rather than its head — a check that moved to the
 * second member would still be reading the first correctly.
 *
 * <p>The order is the table's, and the table's is the file's. What can lose it is a copy: a set that
 * promises membership and not order may be answered in an order the JVM salts per run, which made one
 * source name a different helper on different runs.
 */
class TheRecursiveHelpersAreAnsweredInDeclarationOrderTest {

    private static final List<String> AS_WRITTEN =
            List.of("alpha", "bravo", "charlie", "delta", "echo", "foxtrot");

    private static final String SIX_ON_ONE_CYCLE = """
            module demo

            let alpha (n: Int) : Int = bravo(n)
            let bravo (n: Int) : Int = charlie(n)
            let charlie (n: Int) : Int = delta(n)
            let delta (n: Int) : Int = echo(n)
            let echo (n: Int) : Int = foxtrot(n)
            let foxtrot (n: Int) : Int = alpha(n)
            """;

    private static HelperTable tableOf(String source) {
        Ast.Module parsed = CstFrontend.parse(source);
        Hir.Module resolved = Resolve.module(parsed, SyntaxSymbols.of(parsed, souther.compiler.DefaultStdlib.get()));
        return HelperTable.of(resolved.name(), HelperInliner.helpersOf(resolved),
                Map.of(), Map.of(), InliningPolicy.FULL, souther.compiler.DefaultStdlib.get());
    }

    /** The module's own declarations, in the order the answer holds them. The shipped prelude has
     * recursive helpers of its own and the graph walks those too; which of them there are is not what
     * this is about, and a name the module declares carries no qualifier. */
    private static List<String> declaredHere(Iterable<String> answered) {
        List<String> own = new ArrayList<>();
        for (String name : answered) {
            if (name.indexOf('.') < 0) {
                own.add(name);
            }
        }
        return own;
    }

    @Test
    void theGraphAnswersTheCycleInTheOrderItWasWritten() {
        assertEquals(AS_WRITTEN, declaredHere(HelperGraph.of(tableOf(SIX_ON_ONE_CYCLE)).recursive()));
    }

    @Test
    void theInlinerCarriesTheGraphsOrderRatherThanRebuildingIt() {
        HelperTable table = tableOf(SIX_ON_ONE_CYCLE);
        HelperGraph graph = HelperGraph.of(table);
        List<String> carried = declaredHere(HelperInliner.over(table, graph).recursiveHelpers());
        assertEquals(declaredHere(graph.recursive()), carried);
    }

    /** Declared the other way round, they are answered the other way round: the order is the file's
     * and not a property of the names. */
    @Test
    void theOrderIsTheFilesAndNotTheNames() {
        List<String> reversed = new ArrayList<>(AS_WRITTEN);
        java.util.Collections.reverse(reversed);
        assertEquals(reversed, declaredHere(HelperGraph.of(tableOf("""
                module demo

                let foxtrot (n: Int) : Int = echo(n)
                let echo (n: Int) : Int = delta(n)
                let delta (n: Int) : Int = charlie(n)
                let charlie (n: Int) : Int = bravo(n)
                let bravo (n: Int) : Int = alpha(n)
                let alpha (n: Int) : Int = foxtrot(n)
                """)).recursive()));
    }
}
