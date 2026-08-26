package souther.compiler.inputs;

/**
 * Why the rules a position was owed went unread.
 *
 * <p>What {@link Position#rulesLeftUnread()} used to answer with a boolean. The two facts under it
 * are of different origin — a reading that lost a clause of its own, and a handing over nobody took
 * — and a reader deciding whether one of them is already reported by the finding beside it has to
 * know which. Given the boolean, {@code MeasureClosure} could not know, and reported one stop twice
 * (issue #1084).
 *
 * <p><b>Two levels, because the arms are of two kinds.</b> Whether the rules were this reading's own
 * or somebody else's is the first question; how a handing over came to be unread is the second, and
 * it belongs to the handoff protocol. Written flat, a failure the protocol grows later would widen
 * the vocabulary every reader of this switch has to answer about.
 *
 * <p><b>Determined where it is observed.</b> Each of these is settled by the reader that had both
 * facts in hand and is carried unchanged from there ({@link souther.compiler.partition.ReadingResidue}).
 * Worked out again further down, the answer would be a join of whatever state each phase happened to
 * still be holding — which is how the fact this replaces came to be a boolean in the first place.
 */
public sealed interface RulesLeftUnread {

    /**
     * The reading that owns this position lost a clause of its own.
     *
     * <p>The position was entered. Its rules were there to be read and one of them was not, so the
     * questions standing at it are real questions and this is a finding of its own — never one
     * suppressed because something else was found at the same path.
     */
    record ClauseOfThisReadingWasUnread() implements RulesLeftUnread {}

    /** This position handed its rules on and no reading took them over, in one of the ways a
     *  handing over can be left standing. */
    record Handoff(HandoffUnread why) implements RulesLeftUnread {

        public Handoff {
            if (why == null) {
                throw new IllegalArgumentException(
                        "a handing over unread for no reason is one that was taken over");
            }
        }
    }

    /** How a handing over came to be unread. */
    sealed interface HandoffUnread {

        /**
         * Nothing was opened under the position, because the walk could not go into it.
         *
         * <p>The one arm with a cause named elsewhere. {@link BlockedDescent} is the same stop said
         * from the other end, and it is the one a document reports — so this yields no finding of
         * its own ({@code MeasureClosure}). Kept as an arm all the same: the fold is on this
         * provenance and not on two findings happening to share a path.
         *
         * <p>Only made where a {@link BlockedDescent} was found beside it. That the two agree is a
         * fact about two walks over one model, and it is checked where they are joined rather than
         * assumed by whoever reads this later.
         */
        record FromBlockedDescent() implements HandoffUnread {}

        /**
         * The descent named the positions the rules were passed to, and a reading was not opened at
         * every one of them.
         *
         * <p>Nothing else reports this. The walk did go on, so no {@link BlockedDescent} stands
         * here, and the rules of the positions that got no reading were read by nobody — which
         * raises no question, since a rule nothing read is a rule nothing could find wanting.
         */
        record NotFullyAccepted() implements HandoffUnread {}
    }
}
