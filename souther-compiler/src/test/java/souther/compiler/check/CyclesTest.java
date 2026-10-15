package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.test.OnItsOwnStack;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * Which nodes lie on a cycle and a way round one, over the graphs declarations make.
 */
class CyclesTest {

    /** A node reached from a cycle is not on it, and every member of a group maps to the one set. */
    @Test
    void aGroupIsItsMembersAndNothingTheyReach() {
        Map<String, List<String>> edges = new LinkedHashMap<>();
        edges.put("caller", List.of("ping"));
        edges.put("ping", List.of("pong"));
        edges.put("pong", List.of("ping", "leaf"));
        edges.put("leaf", List.of());
        edges.put("self", List.of("self"));

        Map<String, Set<String>> groups = Cycles.groups(edges);

        assertEquals(Set.of("ping", "pong", "self"), groups.keySet());
        assertEquals(Set.of("ping", "pong"), groups.get("ping"));
        assertSame(groups.get("ping"), groups.get("pong"));
        assertEquals(Set.of("self"), groups.get("self"));
    }

    /** The first way round a depth-first walk meets, taking edges in the order the graph holds them. */
    @Test
    void theWayRoundIsTheFirstTheEdgesInTheirOrderReach() {
        Map<String, List<String>> edges = new LinkedHashMap<>();
        edges.put("a", List.of("b", "c"));
        edges.put("b", List.of("d"));
        edges.put("c", List.of("a"));
        edges.put("d", List.of("a"));

        assertEquals(List.of("a", "b", "d", "a"), Cycles.roundFrom("a", edges));
        assertEquals(List.of(), Cycles.roundFrom("x", Map.of("x", List.of("y"))));
    }

    /** A ring at the far end of a chain, asked of on a small stack: as deep as the chain is long,
     *  a walk on the call stack would not get there. */
    @Test
    void aLongChainIsWalkedWithoutTheCallStack() {
        int links = 100_000;
        Map<Integer, List<Integer>> edges = new LinkedHashMap<>();
        for (int i = 0; i < links; i++) {
            edges.put(i, List.of(i + 1));
        }
        edges.put(links, List.of(links - 1));
        List<Object> answers = OnItsOwnStack.ask("a walk on a small stack", 512L << 10,
                () -> List.of(Cycles.groups(edges), Cycles.roundFrom(links - 1, edges)));

        assertEquals(Set.of(links - 1, links), ((Map<?, ?>) answers.get(0)).keySet());
        assertEquals(List.of(links - 1, links, links - 1), answers.get(1));
    }
}
