package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.core.Core;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A call is seeded where it stands, and not once for every node standing over it.
 *
 * <p>What a behavior's answer guarantees is read ahead of the walk, because a construction is judged
 * at its own step while the answers it is built from stand underneath it. Read from every node of
 * the walk as well, it is read again over the whole of each node's subtree — which decides nothing,
 * since the reading is threaded down and the second lands on the subjects the first wrote, and costs
 * the depth of a body over again at every node of it.
 *
 * <p>Held as a count and not as a duration. What is wrong with reading it again is that the work is
 * quadratic in the depth of a body, and a body twice as deep is the input that says so; a
 * millisecond figure would say it on this machine on this day. Bodies of a nesting the source can
 * write, so what is measured is what an author can hand over.
 *
 * <p>Nothing here reports anything, so this is read off {@link PathEngine#SEEDED} — two readings
 * that differ only in how often they seed answer exactly alike about every program, and a difference
 * nothing can read stops being true without anything failing.
 */
class AnAnswerIsSeededOnceWhereItStandsTest {

    /**
     * A body whose whole of it is one region: {@code depth} calls nested inside one another, with no
     * branch, no block and no binding between them to end the reading early. Each call answers a type
     * with an invariant, so each of them is an answer the seeding reads.
     */
    private static String nested(int depth) {
        StringBuilder call = new StringBuilder("a");
        for (int i = 0; i < depth; i++) {
            call.insert(0, "step(").append(")");
        }
        return """
                module demo exposing ( Amount, step, run )

                data Amount = Int
                    invariant value >= 0

                behavior step : (a: Amount) -> Amount
                    constructs Amount

                let step (a) = Amount(a.value + 1)

                behavior run : (a: Amount) -> Amount
                    constructs Amount

                let run (a) = Amount(%s.value + 1)
                """.formatted(call);
    }

    /** Every answer the check seeded while compiling {@code source}, one entry per seeding. */
    private static List<Core> seededIn(String source) {
        List<Core> seeded = Collections.synchronizedList(new ArrayList<>());
        PathEngine.SEEDED = seeded;
        try {
            Compiler.compileWithWarnings(source);
        } finally {
            PathEngine.SEEDED = null;
        }
        return List.copyOf(seeded);
    }

    @Test
    void aCallNestedInsideAnotherIsSeededOnce() {
        for (int depth : List.of(1, 2, 4, 8, 16)) {
            List<Core> seeded = seededIn(nested(depth));
            assertEquals(depth, seeded.size(),
                    "answers seeded over a body of " + depth + " nested calls");
            Map<Core, Boolean> distinct = new IdentityHashMap<>();
            seeded.forEach(answer -> distinct.put(answer, true));
            assertEquals(seeded.size(), distinct.size(),
                    "one of the " + depth + " nested calls was seeded twice");
        }
    }
}
