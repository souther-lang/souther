package souther.compiler.check;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicReference;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
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
        AtomicReference<Throwable> failed = new AtomicReference<>();
        List<Object> answers = new ArrayList<>();
        Thread walking = new Thread(null, () -> {
            try {
                answers.add(Cycles.groups(edges));
                answers.add(Cycles.roundFrom(links - 1, edges));
            } catch (Throwable e) {
                failed.set(e);
            }
        }, "a small stack", 512L << 10);
        walking.start();
        try {
            walking.join();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            throw new AssertionError(e);
        }

        assertNull(failed.get(), () -> String.valueOf(failed.get()));
        assertEquals(Set.of(links - 1, links), ((Map<?, ?>) answers.get(0)).keySet());
        assertEquals(List.of(links - 1, links, links - 1), answers.get(1));
    }
}
