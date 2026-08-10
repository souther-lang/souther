package souther.runtime;

/**
 * A point the model declared could not arise, reached. The {@code unreachable "reason"} of spec §match
 * states an assumption the callee cannot derive — a fact about the world, or what a caller has
 * already ruled out — so reaching it means that assumption does not hold, which is a model bug and
 * not a business result.
 *
 * <p>It aborts as an invariant violation does, and for the same reason it is a different type from
 * {@link ConstraintViolation}: what failed there is a value against its type's condition, and what
 * failed here is a premise the model wrote down. Both reach a boundary as an abort a business
 * failure is distinguished from (spec §jvm-abort).
 */
public final class UnreachableReached extends RuntimeException {

    public UnreachableReached(String message) {
        super(message);
    }

    /**
     * Aborts with {@code message}. Declared to answer a value so the emitted code reads as an
     * expression like any other — the position it stands in has a value on the stack in every path
     * the verifier walks, and nothing follows it at run time.
     */
    public static Object reached(String message) {
        throw new UnreachableReached(message);
    }
}
