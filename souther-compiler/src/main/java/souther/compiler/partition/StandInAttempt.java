package souther.compiler.partition;

/**
 * What came of standing a behavior's dependencies in for one way, and what the standing-in was
 * arrived at without.
 *
 * <p>A product because the two are independent, which is what the case a reader most needs shows: a
 * value for a dependency that meets none of what the way asks of it still leaves a row where the
 * module states a table the row can lean on, so the outcome is a row and the account is not empty.
 * Held on the arm that came to nothing, that row would go out with nothing said about what it was
 * composed without — and a run of it that lands somewhere else would be read as the model's answer.
 *
 * <p>Which also keeps {@link AnswersStoodIn} what it is. What a row stands its dependencies in with
 * is one question; what the reading and the composer could not act on is another, and a field added
 * to the answer would be the second question asked of the first one's arms.
 */
public record StandInAttempt(AnswersStoodIn outcome, CompositionAccount account) {

    /** One that stands nothing in and leaves nothing out, which is what a behavior requiring
     *  nothing has. */
    public static final StandInAttempt REQUIRING_NOTHING =
            new StandInAttempt(AnswersStoodIn.REQUIRING_NOTHING, CompositionAccount.NOTHING);

    public StandInAttempt {
        if (outcome == null || account == null) {
            throw new IllegalArgumentException(
                    "standing the dependencies in came to something, and says what it left out");
        }
    }
}
