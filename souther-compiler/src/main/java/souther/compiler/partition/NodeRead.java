package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.inputs.InputReads;

/**
 * A node of a body as one reading of it arrives there: the node, and the names in force.
 *
 * <p>The node by identity and the names by what they say. Which node a reading is at is an
 * identity question: a node is the same place as itself and as nothing else, and asking a whole
 * subtree whether it says what another says would make the key cost as much as the tree under it.
 * The names are what they say and not which object says them: a {@code let} body reached by two
 * walks is under two environments built the same way, and read as two places what is worked out
 * inside it would be worked out twice.
 *
 * @param node  where the reading is
 * @param reads the names in force there
 */
record NodeRead(Core node, InputReads reads) {

    @Override
    public boolean equals(Object other) {
        return other instanceof NodeRead that && node == that.node && reads.equals(that.reads);
    }

    @Override
    public int hashCode() {
        return System.identityHashCode(node) * 31 + reads.hashCode();
    }
}
