package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.StringJoiner;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A record holding the one before it in a field, down to a number with a rule on it: each record
 * reads that rule at a projection as long as the chain under it, and its positions stop well short
 * of the end. Which of the projection's shorter projections is a position is asked going down the
 * names once, and not by naming each of them — each such name is a term as long as itself, so named
 * one at a time, every record costs the square of its depth and the chain the cube of its length.
 *
 * <p>Held as a count of the walks the naming starts and not as a time, over a doubling, so the
 * property asked is the shape of the growth: named one at a time, the walks alone grow with the
 * square of the chain.
 */
class ARuleUnderAChainOfRecordsNamesItsProjectionOnceTest {

    private static String chainOf(int links) {
        StringJoiner exposed = new StringJoiner(", ");
        StringBuilder decls = new StringBuilder("data T1 = Int\n    invariant value >= 1 && value <= 9\n");
        exposed.add("T1");
        for (int i = 2; i <= links; i++) {
            exposed.add("T" + i);
            decls.append("data T").append(i).append(" = { x: T").append(i - 1).append(" }\n");
        }
        return "module chain exposing ( " + exposed + " )\n\n" + decls;
    }

    /** How many canonical-key walks compiling a chain of {@code links} records starts. */
    private static long walksOver(int links) {
        String src = chainOf(links);
        long[] counting = {0};
        Terms.COUNTING_WALKS = counting;
        try {
            Compiler.compile(src);
        } finally {
            Terms.COUNTING_WALKS = null;
        }
        return counting[0];
    }

    @Test
    void doublingTheChainAboutDoublesTheWalks() {
        Map<Integer, Long> walks = new LinkedHashMap<>();
        for (int links : new int[] {40, 80, 160}) {
            walks.put(links, walksOver(links));
        }
        assertTrue(walks.get(80) <= walks.get(40) * 5 / 2, "80 records: " + walks);
        assertTrue(walks.get(160) <= walks.get(80) * 5 / 2, "160 records: " + walks);
    }
}
