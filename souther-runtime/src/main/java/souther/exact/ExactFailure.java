package souther.exact;

/**
 * Where exact arithmetic could not give an answer, in the two ways that differ for whoever asked.
 *
 * <p>An {@link ExactRangeExceeded} says the answer has no representation: an exponent past sixty-four
 * bits, or a whole number past what the host addresses. An {@link ExactRoomExceeded} says this run had
 * no room for an instrument the answer needed, and a run with more room answers. The arithmetic
 * reports which; what each becomes is the caller's vocabulary, so the caller translates.
 *
 * <p>An {@link ArithmeticException} so that a caller with no vocabulary of its own passes it on as
 * the failure of an arithmetic operation, which is what it is.
 */
public abstract sealed class ExactFailure extends ArithmeticException
        permits ExactRangeExceeded, ExactRoomExceeded {
    private static final long serialVersionUID = 1L;

    private final String reason;

    ExactFailure(String reason) {
        super(reason);
        this.reason = reason;
    }

    /** What was refused, which {@link #getMessage} says too but is not known to be present. */
    public String reason() {
        return reason;
    }
}
