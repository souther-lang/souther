package souther.compiler.report;

import souther.compiler.observe.FailurePhase;

/**
 * Where a row that does not hold stopped, as a report says it.
 *
 * <p>A row does not hold for more than one reason, and only one of them is the behavior answering
 * other than the row states. One whose input could not be built never applied the behavior; one
 * whose expectation could not be built applied nothing either. What each of them reached before it
 * stopped is what it covers, so they are all rows that do not hold — and a reader told only that
 * would take every one of them for a wrong answer, so the place it stopped travels with it.
 *
 * <p>Only the places a row can fail at. A run that went over a budget, ran out of stack or could
 * not be handed over ends undecided rather than failed, and is no row that does not hold.
 */
public enum RowFailure {

    /** An input could not be built, so the behavior was never applied. */
    INPUT_FIXTURE("its input could not be built"),

    /** What the row expects could not be built, or names a case the behavior cannot produce. */
    EXPECTED_FIXTURE("what it expects could not be built"),

    /** A dependency had no fake, or the fake had no answer for what it was given. */
    FAKE_RESOLUTION("a dependency had no fake for it"),

    /** What the row states does not keep what the behavior declares of its answer. */
    ENSURES("what it states breaks what the behavior ensures"),

    /** Applying the behavior produced no answer. */
    INVOCATION("applying the behavior gave no answer"),

    /** The behavior answered, and not with what the row expects. */
    COMPARISON("the behavior answered otherwise");

    private final String said;

    RowFailure(String said) {
        this.said = said;
    }

    /** How a line of a page says it. */
    public String said() {
        return said;
    }

    /**
     * Where a failed row stopped. Every place but these ends a row undecided, so a row that failed
     * anywhere else is two of this compiler's answers disagreeing about what failing is.
     */
    public static RowFailure of(FailurePhase phase) {
        return switch (phase) {
            case INPUT_FIXTURE -> INPUT_FIXTURE;
            case EXPECTED_FIXTURE -> EXPECTED_FIXTURE;
            case FAKE_RESOLUTION -> FAKE_RESOLUTION;
            case ENSURES -> ENSURES;
            case INVOCATION -> INVOCATION;
            case COMPARISON -> COMPARISON;
            case NONE, ANSWERER_ESTABLISHMENT, IMPLEMENTATION_NOT_MADE, VALUE_CROSSING, STEP_LIMIT,
                 DEPTH_LIMIT, TIMEOUT, STACK_EXHAUSTED -> throw new IllegalStateException(
                    "a row that failed stopped where a row ends undecided: " + phase);
        };
    }
}
