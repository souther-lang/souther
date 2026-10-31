package souther.compiler.core;

import souther.compiler.diag.SourcePos;
import souther.compiler.types.BinOp;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@link Core#forEachDistinctNode} meets a node once however many slots hold it, and tells nodes
 * apart by identity and not by what they equal.
 */
class ASharedNodeIsVisitedOnceByTheDistinctWalkTest {

    private static final SourcePos POS = new SourcePos(0, 0);

    private static Core.Int two() {
        return new Core.Int(2, Type.INT, POS);
    }

    private static Core sum(Core left, Core right) {
        return new Core.Binary(BinOp.ADD, left, right, Core.BinaryReading.AS_THEY_STAND,
                ConstructOccurrence.unwritten(), Type.INT, POS);
    }

    private static List<Core> visited(Core root) {
        List<Core> out = new ArrayList<>();
        Core.forEachDistinctNode(root, out::add);
        return out;
    }

    /** Each level names the one below it twice, so the tree walk would make 2^31 - 1 visits. */
    @Test
    void aChainNamingTheLevelBelowTwiceVisitsOneNodePerLevel() {
        Core e = two();
        for (int i = 0; i < 30; i++) {
            e = sum(e, e);
        }

        assertEquals(31, visited(e).size());
    }

    @Test
    void twoNodesThatAreEqualButNotTheSameAreBothVisited() {
        Core one = two();
        Core other = two();
        assertEquals(one, other);

        List<Core> seen = visited(sum(one, other));

        assertEquals(3, seen.size());
    }

    /** A second walk over the same nodes sees all of them: what the first met is not remembered. */
    @Test
    void theRecordOfNodesSeenLastsOneCall() {
        Core shared = two();
        Core root = sum(shared, shared);

        List<Core> first = visited(root);
        List<Core> second = visited(root);

        assertEquals(2, first.size());
        assertEquals(2, second.size());
        assertTrue(second.stream().anyMatch(node -> node == root));
        assertTrue(second.stream().anyMatch(node -> node == shared));
    }

    @Test
    void aWidenAndWhatItHoldsAreBothVisited() {
        Core.Int held = two();
        Core.Widen widened = new Core.Widen(held, Type.DECIMAL);

        List<Core> seen = visited(widened);

        assertEquals(2, seen.size());
        assertTrue(seen.stream().anyMatch(node -> node == widened));
        assertTrue(seen.stream().anyMatch(node -> node == held));
    }
}
