package souther.exact;

/**
 * One of each way the exact arithmetic fails, for a test of what a caller makes of them.
 *
 * <p>Built here because the arithmetic keeps its failures to itself, and one of them is not reached
 * by any sum or difference this compiler asks for: a run short of room is met by an instrument, and
 * a test holding a caller to its translation needs both in hand.
 */
public final class ExactFailures {

    private ExactFailures() {
    }

    /** A run that had no room for what the answer needed. */
    public static ExactFailure room() {
        return new ExactRoomExceeded("no room, for a test");
    }

    /** An answer with no representation. */
    public static ExactFailure range() {
        return new ExactRangeExceeded("no representation, for a test");
    }
}
