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
 * recording as long as the list. It is a bound on what a claim can name, and not a consequence of
 * how many combinations a group is offered under: an evaluation's number is the application's
 * place among the elements a closure was handed, which a flatMap or a filter can leave far past the
 * count of decisions made of it. A claim is refused a visit past this ({@link ControlClaim.Visit}),
 * and a reading with a decision about one says it did not ask.
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
