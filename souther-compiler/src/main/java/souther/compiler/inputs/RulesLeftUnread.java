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

    /**
     * This position handed its rules on, the descent named the positions they were passed to, and a
     * reading was not opened at every one of them.
     *
     * <p>The walk did go on, and the rules of the positions that got no reading were read by
     * nobody — which raises no question, since a rule nothing read is a rule nothing could find
     * wanting. A handing over with no recipient named at all is not this: it is the walk
     * contradicting itself, and the ledger refuses it ({@link RuleHandoffs#standingAt}).
     */
    record HandoffNotAccepted() implements RulesLeftUnread {}
}
