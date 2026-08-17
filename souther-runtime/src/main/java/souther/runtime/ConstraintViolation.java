package souther.runtime;

/**
 * A constraint the model declared cannot be broken, broken while the domain ran — the abort of spec
 * §algebraic-types, §violation-destination, §jvm-abort. The model states one in two places and both
 * leave by this: a {@code data}'s {@code invariant}, which every construction of that type owes, and
 * a {@code behavior}'s {@code ensures}, which relates what the behavior is given to what it answers.
 * Either is a model bug and not a business result, so neither has a place in an output sum (spec
 * §unmarked-sum) and the computation aborts rather than answering.
 *
 * <p>What broke is a {@link ConstraintFailure}, which says which of the two it was. A third origin is
 * a case written there rather than one of those two stretched to carry it, and it reaches this by the
 * same {@link #notHeld} — so an origin being added is not a second way to abort.
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
    /**
     * The abort a broken constraint leaves by.
     *
     * <p>One entry and not one per origin. What a caller has is a failure that says what it is, so an
     * overload per kind would be this deciding again what the value already answers — and the day a
     * third origin is written, an overload it forgot would be an origin that aborts some other way.
     */
    public static ConstraintViolation notHeld(ConstraintFailure failure) {
        return new ConstraintViolation(failure.toString());
    }

    public static Object orThrow(Result<?, ?> r) {
        if (r instanceof Result.Ok<?, ?> ok) {
            return ok.value();
        }
        throw new ConstraintViolation(String.valueOf(((Result.Err<?, ?>) r).error()));
    }
}
