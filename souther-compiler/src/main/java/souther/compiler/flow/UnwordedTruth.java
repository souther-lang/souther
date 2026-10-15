package souther.compiler.flow;

import souther.compiler.core.Core;

import java.util.Objects;

/**
 * A truth written as {@code truth} that came out {@code held} on a way, where the naming had no
 * words for it.
 *
 * <p>Which way it came out is known all the same, and kept: a truth the body was handed comes out
 * a way at no construct the naming places, and an arm a run on the way goes into is somewhere the
 * run is seen — so the arm can say what the walk could not.
 *
 * <p>Compared by the node and not by what it says: a node occurs once, and two truths written alike
 * in two places are two parts, each of which a reader finds where it is written. Compared by what
 * it says, the hash of a way would walk the tree under every truth on it.
 */
public record UnwordedTruth(Core truth, boolean held) {

    public UnwordedTruth {
        Objects.requireNonNull(truth, "a truth is written somewhere");
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof UnwordedTruth that && that.truth == truth && that.held == held;
    }

    @Override
    public int hashCode() {
        return System.identityHashCode(truth) * 31 + Boolean.hashCode(held);
    }
}
