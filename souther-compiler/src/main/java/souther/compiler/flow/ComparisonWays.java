package souther.compiler.flow;

import souther.compiler.core.Core;

import java.util.function.Function;

/**
 * Whether a value stands behind one way of settling an expression.
 *
 * <p>What the reading of a body asks before it holds a way at all, and the one thing about a body
 * this reading does not work out for itself. Whether some value brings a comparison out a given way
 * is a question about the number the comparison is over — where its values run, and whether any of
 * them falls on the side the way needs — and the number is named by a reading of the input this
 * package does not have and should not repeat.
 *
 * <p>Asked one way at a time, and a way nothing stands behind is not answered here: {@code a == a}
 * comes out one way and {@code 1 > 2} comes out one way, while a rule about the shape of the node
 * would say both come out two.
 *
 * <p>Handed to the reading rather than taken off the naming. What a body does is settled with no
 * naming at all, so a question the naming answered would put the numbering back in charge of what
 * the body does — which is what {@link ValueArrivals} exists to keep apart. The same answer serves
 * both halves.
 */
public interface ComparisonWays {

    /**
     * Whether a value of what {@code e} is over brings it out {@code want}.
     *
     * @param settledBy what a name was bound to, or null where the body bound it to nothing this can
     *                  read — a parameter, an arm's binding, a value handed in from outside
     */
    boolean comesOut(Core e, boolean want, Function<Core.Read, Core> settledBy);

    /**
     * What the body's own text says, for a reading with no input to ask about.
     *
     * <p>Under-reading: what it is sure of is the primitives' ranges, and a way it cannot place a
     * value behind is one it says nothing about. A reader that has the input's rules in hand answers
     * more of them and answers them the same way.
     */
    ComparisonWays OF_THE_TREE = Witnessed::comesOut;
}
