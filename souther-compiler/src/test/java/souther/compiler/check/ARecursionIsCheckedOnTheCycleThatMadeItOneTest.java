package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.types.ReachName;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A helper the call graph says recurses is proven total over the call cycle it is on, and a graph
 * that answers it no such cycle is refused rather than read.
 *
 * <p>The size-change criterion is a claim about every graph in a group, and it holds of a group with
 * none. So a helper whose group came out empty would be accepted as total without one of its calls
 * being read. The call graph answers which helpers recurse and which cycle each is on with one
 * predicate; the graph handed in here is one whose two answers disagree, which is what a change to
 * either of them could make, and the check has to stop there.
 */
class ARecursionIsCheckedOnTheCycleThatMadeItOneTest {

    private static final String ONE_HELPER_THAT_CALLS_NOTHING = """
            module demo

            let lone (n: Int) : Int = n
            """;

    private static HelperTable tableOf(String source) {
        Ast.Module parsed = CstFrontend.parse(source);
        Hir.Module resolved = Resolve.module(parsed, SyntaxSymbols.of(parsed, DefaultStdlib.get()));
        return HelperTable.of(resolved.name(), HelperInliner.helpersOf(resolved),
                Map.of(), Map.of(), InliningPolicy.FULL, DefaultStdlib.get());
    }

    private static ReachName.Declaration own(String name) {
        return new ReachName.Own(new ValueName.Helper("demo", name));
    }

    @Test
    void aRecursionOnNoCycleIsRefused() {
        HelperTable table = tableOf(ONE_HELPER_THAT_CALLS_NOTHING);
        HelperGraph disagreeing =
                new HelperGraph(HelperGraph.of(table).callsOf(), List.of(own("lone")));

        assertThrows(IllegalStateException.class,
                () -> TotalityChecker.check(HelperInliner.over(table, disagreeing)));
    }

    /** The control: the same module, answered by the graph built over it, has nothing to prove. */
    @Test
    void theSameHelperAnsweredByItsOwnGraphIsNotARecursion() {
        HelperTable table = tableOf(ONE_HELPER_THAT_CALLS_NOTHING);

        assertDoesNotThrow(
                () -> TotalityChecker.check(HelperInliner.over(table, HelperGraph.of(table))));
    }
}
