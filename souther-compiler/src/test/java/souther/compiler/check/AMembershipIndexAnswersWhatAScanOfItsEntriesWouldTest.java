package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.types.ReachName;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * Which helpers recurse, and which of them a module holds, are asked once for every call while
 * bodies are expanded, so both are answered from an index rather than by scanning. An index is a
 * second way of holding the same entries, and these hold it to answering what the scan would.
 *
 * <p>The recursions are also an ordered answer: a graph is compared by them, and the order is part
 * of what it means. Held with an index, they are still the sequence they were and nothing more.
 */
class AMembershipIndexAnswersWhatAScanOfItsEntriesWouldTest {

    private static final String A_CYCLE_A_CALLER_AND_A_VALUE = """
            module demo

            let caller (n: Int) : Int = ping(n)
            let ping (n: Int) : Int = pong(n)
            let pong (n: Int) : Int = ping(n)
            let alone (n: Int) : Int = alone(n)
            let seed : Int = caller(1)
            """;

    private static HelperTable tableOf(String source) {
        Ast.Module parsed = CstFrontend.parse(source);
        Hir.Module resolved = Resolve.module(parsed, SyntaxSymbols.of(parsed, DefaultStdlib.get()));
        return HelperTable.of(resolved.name(), HelperInliner.helpersOf(resolved),
                Map.of(), InliningPolicy.FULL, DefaultStdlib.get());
    }

    private static ReachName.Declaration own(String name) {
        return new ReachName.Own(new ValueName.Helper("demo", name));
    }

    /** Everything the table reaches — the module's own and the prelude's — and one name it does not. */
    private static List<ReachName.Declaration> asked(HelperTable table) {
        List<ReachName.Declaration> asked = new ArrayList<>(table.reachable().keySet());
        asked.add(own("nobodyWroteThis"));
        return asked;
    }

    @Test
    void whetherAHelperRecursesIsWhatTheListOfRecursionsHolds() {
        HelperGraph graph = HelperGraph.of(tableOf(A_CYCLE_A_CALLER_AND_A_VALUE));
        List<ReachName.Declaration> scanned = new ArrayList<>(graph.recursive());

        for (ReachName.Declaration each : asked(tableOf(A_CYCLE_A_CALLER_AND_A_VALUE))) {
            assertEquals(scanned.contains(each), graph.recurses(each), each.rendered());
        }
    }

    @Test
    void whetherTheModuleHoldsAHelperIsWhatItsEntriesSay() {
        HelperTable table = tableOf(A_CYCLE_A_CALLER_AND_A_VALUE);

        for (ReachName.Declaration each : asked(table)) {
            boolean scanned = false;
            for (HelperEntry entry : table.held().values()) {
                scanned |= entry.reachedAs().equals(each);
            }
            assertEquals(scanned, table.holds(each), each.rendered());
        }
    }

    @Test
    void theRecursionsAreComparedAsTheSequenceTheyAreHeldIn() {
        HelperGraph graph = new HelperGraph(Map.of(), List.of(own("ping"), own("pong")));

        assertEquals(List.of(own("ping"), own("pong")), graph.recursive());
        assertEquals(graph.recursive(), List.of(own("ping"), own("pong")));
        assertEquals(List.of(own("ping"), own("pong")).hashCode(), graph.recursive().hashCode());
        assertEquals(new HelperGraph(Map.of(), List.of(own("ping"), own("pong"))), graph);
    }

    @Test
    void soTheSameRecursionsInAnotherOrderAreAnotherAnswer() {
        HelperGraph graph = new HelperGraph(Map.of(), List.of(own("ping"), own("pong")));

        assertNotEquals(List.of(own("pong"), own("ping")), graph.recursive());
        assertNotEquals(new HelperGraph(Map.of(), List.of(own("pong"), own("ping"))), graph);
    }
}
