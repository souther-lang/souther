package souther.compiler.coverage;

/**
 * One condition coming out one way on one of the times a run visited it, as a run records it.
 *
 * <p>A place a run comes back to is recorded by {@link RecordedConditionOutcome} as the ways it
 * came out and nothing of which visit each did, so a run that had it hold once and fail once reads
 * the same whichever came first. What a reading can say is which visit belongs to which value, and
 * that is a claim about the evidence ({@link ControlClaim.Visit}); this is the evidence that can
 * answer it.
 *
 * <p>Counted by the recording and not by the probed class, which writes the same call at every
 * visit: the nth is how many times this thread has recorded the condition since the row began.
 *
 * <p><b>Why this many.</b> The recording is bounded so that a loop over a long list cannot make a
 * recording as long as the list. A group of combinations is offered only under a budget that is an
 * {@code int}, and a group of more than thirty factors of two outcomes apiece is past every such
 * budget: it is held back without a run being asked about any of its claims. So no claim that is
 * asked of a recording names a visit this does not keep, and a list longer than this is a group not
 * measured rather than a group that does not exist.
 *
 * @param at    the number the run was recorded at
 * @param nth   which visit of the run, counting from none
 * @param held  the way it came out
 */
public record RecordedVisit(int at, int nth, boolean held) {

    /** How many visits to one condition a run records. */
    public static final int MOST = 32;

    public RecordedVisit {
        if (at < 0) {
            throw new IllegalArgumentException(
                    "a run is recorded at a number the emitter wrote: " + at);
        }
        if (nth < 0 || nth >= MOST) {
            throw new IllegalArgumentException(
                    "a run records the first " + MOST + " visits to a condition, not visit " + nth);
        }
    }

    @Override
    public String toString() {
        return "site@" + at + " visit " + nth + (held ? " held" : " failed");
    }
}
