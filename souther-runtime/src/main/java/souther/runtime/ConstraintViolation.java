package souther.runtime;

/**
 * A domain invariant broken inside the domain — the abort of spec §algebraic-types, §violation-destination,
 * §jvm-abort. When a behavior constructs invariant-bearing data whose invariant fails, the computation aborts
 * by throwing this instead of returning a business case: an invariant violation is a model bug, not a
 * business result, so it has no place in the output sum (spec §unmarked-sum).
 *
 * <p>Souther code cannot catch it (there is no catch syntax), so it never drives business flow
 * (spec §out-of-scope). A boundary (e.g. HTTP) may catch it and map it to a 500 — distinct from a business
 * failure, which arrives as an output case and maps to a 400 (spec §jvm-abort). Decode-side violations
 * are different: they are carried by Raoh's {@code Result} failure, not by this (spec §decoder-error).
 */
public final class ConstraintViolation extends RuntimeException {

    public ConstraintViolation(String message) {
        super(message);
    }

    /**
     * Turns a construction result into a plain value or an abort: the constructed value when the
     * invariants held, or a thrown {@link ConstraintViolation} carrying the message when they did
     * not. Generated behavior bodies call this so a construction never surfaces a {@code Result}
     * on a public API and a violation never rides an output case.
     */
    public static Object orThrow(Result<?, ?> r) {
        if (r instanceof Result.Ok<?, ?> ok) {
            return ok.value();
        }
        throw new ConstraintViolation(String.valueOf(((Result.Err<?, ?>) r).error()));
    }
}
