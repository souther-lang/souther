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
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A body reaches a declaration by calling it or by reading it, and only a call is an edge of
 * recursion.
 *
 * <p>A value that calls a helper which reads the value back closes a cycle of what runs, and that
 * cycle is refused elsewhere, as a value that reaches itself. It is not a recursion: nothing in it is
 * lowered to a method and left calling itself. The call graph that answers which helpers recurse
 * counts the call and not the read, and the edges a body has are sorted into the two before any
 * graph is built, so a reader that wants both asks for both.
 */
class ARecursionIsACycleOfCallsAndNotOfReadsTest {

    private static final String A_VALUE_AND_THE_HELPER_IT_CALLS = """
            module demo

            let seed = f(1)
            let f (n: Int) : Int = n + seed
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

    private static HelperEdges edgesOf(HelperTable table, String name) {
        return HelperEdges.in(table.library(), table.reached(own(name)).writtenBody(),
                table.reachable());
    }

    @Test
    void aValueThatAppliesAHelperCallsIt() {
        HelperEdges seed = edgesOf(tableOf(A_VALUE_AND_THE_HELPER_IT_CALLS), "seed");

        assertEquals(Set.of(own("f")), seed.calls());
        assertEquals(Set.of(), seed.valueReads());
    }

    @Test
    void aHelperThatNamesAValueReadsIt() {
        HelperEdges f = edgesOf(tableOf(A_VALUE_AND_THE_HELPER_IT_CALLS), "f");

        assertEquals(Set.of(), f.calls());
        assertEquals(Set.of(own("seed")), f.valueReads());
    }

    @Test
    void soTheCycleTheyCloseIsNoRecursion() {
        HelperGraph graph = HelperGraph.of(tableOf(A_VALUE_AND_THE_HELPER_IT_CALLS));

        assertFalse(graph.recurses(own("f")));
        assertFalse(graph.recurses(own("seed")));
        assertEquals(List.of(), graph.callCycleOf(own("f")));
    }

    /** A helper that takes arguments, written where a value goes, becomes a function there. Nothing
     * runs it at that point, and applying the parameter it arrives in applies no declaration. */
    @Test
    void aHelperNamedWhereAValueGoesIsNeitherCalledNorRead() {
        HelperTable table = tableOf("""
                module demo

                let twice (n: Int) : Int = n + n
                let apply (g: (Int) -> Int) : Int = g(1)
                let used : Int = apply(twice)
                """);

        assertEquals(Set.of(own("apply")), edgesOf(table, "used").calls());
        assertEquals(Set.of(), edgesOf(table, "used").valueReads());
        assertEquals(Set.of(), edgesOf(table, "apply").calls());
    }

    @Test
    void aCycleIsAnsweredWithEveryMemberInTheOrderTheyWereDeclared() {
        HelperGraph graph = HelperGraph.of(tableOf("""
                module demo

                let caller (n: Int) : Int = ping(n)
                let ping (n: Int) : Int = pong(n)
                let pong (n: Int) : Int = ping(n)
                """));

        assertEquals(List.of(own("ping"), own("pong")), graph.callCycleOf(own("ping")));
        assertEquals(List.of(own("ping"), own("pong")), graph.callCycleOf(own("pong")));
    }

    /** Reaching a cycle is not being on it. */
    @Test
    void aHelperThatOnlyCallsIntoACycleIsOnNone() {
        HelperGraph graph = HelperGraph.of(tableOf("""
                module demo

                let caller (n: Int) : Int = ping(n)
                let ping (n: Int) : Int = pong(n)
                let pong (n: Int) : Int = ping(n)
                """));

        assertFalse(graph.recurses(own("caller")));
        assertEquals(List.of(), graph.callCycleOf(own("caller")));
        assertTrue(graph.recurses(own("ping")));
    }
}
