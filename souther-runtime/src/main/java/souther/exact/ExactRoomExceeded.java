package souther.exact;

/** The run had no room for an instrument the answer needed; a run with more room gives the answer. */
public final class ExactRoomExceeded extends ExactFailure {
    private static final long serialVersionUID = 1L;

    ExactRoomExceeded(String message) {
        super(message);
    }
}
