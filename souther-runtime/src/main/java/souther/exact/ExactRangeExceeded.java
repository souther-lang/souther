package souther.exact;

/** The answer has no representation: not a shortage of room, and no run with more room gives one. */
public final class ExactRangeExceeded extends ExactFailure {
    private static final long serialVersionUID = 1L;

    ExactRangeExceeded(String message) {
        super(message);
    }
}
