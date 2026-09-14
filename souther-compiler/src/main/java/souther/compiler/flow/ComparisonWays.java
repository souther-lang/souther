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
     * The same, inside a body that binds {@code binder} to {@code value}.
     *
     * <p>Scoped like the naming and for the same reason: what a name reads is not a fact about the
     * node that reads it. A comparison written under {@code let len = String.length(c)} is about the
     * length, and a reading that stayed outside the binding would find no number named there —
     * leaving the way unheld under a binding and held without one, which is a {@code let} changing
     * what the body does.
     */
    ComparisonWays under(Core.Binder binder, Core value);

    /** The same, inside {@code arm} of {@code match}. The other place what a name means changes,
     *  and a reading that has one of the two and not the other is scoped like nothing else here. */
    ComparisonWays insideArm(Core.Match match, Core.Case arm);

    /**
     * What the body's own text says, for a reading with no input to ask about.
     *
     * <p>Under-reading: what it is sure of is the primitives' ranges, and a way it cannot place a
     * value behind is one it says nothing about. A reader that has the input's rules in hand answers
     * more of them and answers them the same way. Nothing a name is bound to changes what the text
     * says, so this is the same reading inside every scope.
     */
    ComparisonWays OF_THE_TREE = new ComparisonWays() {
        @Override
        public boolean comesOut(Core e, boolean want, Function<Core.Read, Core> settledBy) {
            return Witnessed.comesOut(e, want, settledBy);
        }

        @Override
        public ComparisonWays under(Core.Binder binder, Core value) {
            return this;
        }

        @Override
        public ComparisonWays insideArm(Core.Match match, Core.Case arm) {
            return this;
        }
    };
}
