package souther.compiler.check;

import souther.compiler.numeric.OrderedIntervals;
import souther.compiler.values.Allowance;
import souther.compiler.values.Emptiness;
import souther.compiler.values.PlannedValues;

/**
 * What every clause of one value says between them, with the choices still open.
 *
 * <p>One of two trees over the same clauses, and the one that derives values. Which values a
 * position may take is settled by every rule of the declaration together, so a conjunction here
 * distributes over a choice ({@link #meet}) and a branch is refined by clauses its author wrote
 * elsewhere. Which rules each clause took in is not here at all: that is a question about one
 * rule's own clauses, answered over {@link StatedByClauses}, and a constraint distributed in from a
 * neighbouring rule must not answer it. This type has no account to contaminate, and the account's
 * type has no way to take another rule's reading in — the separation is the two types.
 *
 * <p>What the two share is the choices. A {@link Choice} here carries the {@link ChoiceId} of the
 * written {@code ||} it came from, and settling this tree is what decides, for every id, whether
 * anybody can be in each of its branches ({@link Settlement}). The account reads that decision; it
 * never makes one.
 */
sealed interface StatedTogether {

    /** What the clauses reaching here leave, in both languages. */
    record Said(PlannedValues<FactSubject> values, OrderedIntervals<FactSubject> ordered)
            implements StatedTogether, Confinement<FactSubject> {

        /**
         * What the values leave, as far as that is settled without building anything.
         *
         * <p>A description of what a position admits is not a set, so the alternatives cannot be
         * asked where their positions stop: which strings a pattern names is a machine somebody has
         * to make, and making one here is the work this reading exists to put off. What is settled
         * before that — a description that already says it admits nothing — is settled, and the rest
         * waits.
         */
        @Override
        public Emptiness ofTheValues() {
            return values.emptiness();
        }

        /**
         * The same, out of what was built for the positions rather than by building.
         *
         * <p>A description settled empty is settled whoever asks; where it is not, what stands is
         * whatever the answer being put together has already worked out at those positions.
         */
        @Override
        public Emptiness ofTheValuesAlreadyBuilt(Allowance<FactSubject> by) {
            return values.holdsNothingAsBuilt(by) ? Emptiness.EMPTY : Emptiness.UNDECIDED;
        }
    }

    /**
     * A choice whose branches are not settled yet, standing for the written {@code ||} named by
     * {@code id} — one of however many places distribution put it.
     */
    record Choice(ChoiceId id, StatedTogether left, StatedTogether right)
            implements StatedTogether {

        public Choice {
            if (id == null || left == null || right == null) {
                throw new IllegalArgumentException("a choice is between two named readings");
            }
        }
    }

    /** Nothing read, so nothing ruled out — the identity of {@link #meet}. */
    static StatedTogether top() {
        return new Said(PlannedValues.top(), OrderedIntervals.top());
    }

    /**
     * Both holding at once, distributed over every choice still open.
     *
     * <p>A conjunction of a choice is the choice between the conjunctions, and the id goes with
     * each copy: what is multiplied is where the branch stands, never which written choice it is a
     * branch of.
     */
    default StatedTogether meet(StatedTogether other) {
        if (this instanceof Choice it) {
            return new Choice(it.id(), it.left().meet(other), it.right().meet(other));
        }
        if (other instanceof Choice it) {
            return new Choice(it.id(), meet(it.left()), meet(it.right()));
        }
        Said here = (Said) this;
        Said there = (Said) other;
        return new Said(here.values().meet(there.values()),
                here.ordered().meet(there.ordered()));
    }
}
