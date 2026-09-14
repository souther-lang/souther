package souther.compiler.check;

import souther.compiler.core.Core;

import java.util.function.Function;

/**
 * Whether a rule is about how one position stands against another.
 *
 * <p>One rule about the shape, asked by every reader that has to tell a relation apart from anything
 * else. The two readings of a clause look positions up differently — one asks what a term is called
 * where a size call is known by its own name, the other asks what a value's position is called — and
 * that difference is each reader's own. Which shapes count as relating two positions is not: read
 * apart, one reader would call {@code a /= b} a form it could not take in while the other called it
 * a relation, and the word each is projected to tells the author two different things about one
 * clause.
 *
 * <p>Another position, and not a position on each side. {@code value == value} has two operands and
 * one position, and calling it a relation says the rule compares the position to another — which the
 * model did not write.
 */
final class Relates {

    /**
     * Whether {@code e} compares one of the positions being read with another of them.
     *
     * @param positionIn what a side of the comparison is a position of, or null where it is not one
     *                   of the positions this reader is about. The reader's own, because how a
     *                   position is looked up is a fact about the reading and not about the shape
     */
    static boolean twoPositions(Core e, Function<Core, Object> positionIn) {
        // Which operators compare is the one place that says so. Everything else is read as
        // whatever else it is, since what a call or a pattern says about the positions in it is
        // what a reading could not work out — counting the positions instead reads
        // `validPair(left, right)` as a relation, which it may not be.
        if (!(e instanceof Core.Binary b) || !b.op().compares()) {
            return false;
        }
        Object left = positionIn.apply(b.left());
        Object right = positionIn.apply(b.right());
        return left != null && right != null && !left.equals(right);
    }

    private Relates() {}
}
