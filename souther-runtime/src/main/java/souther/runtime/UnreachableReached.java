package souther.runtime;

import org.jspecify.annotations.Nullable;

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
 *
 * <p>Where the {@code unreachable} is written travels as data beside the message, as a refused
 * construction's site does: the module whose text it is written in, and the line and column in
 * that text. A body inlined from another module's helper runs in this module's class, and the
 * class's line table names only this module's text, so the site is not read off the frame. Where
 * the code that reached it had no place for it, there is none.
 */
public final class UnreachableReached extends RuntimeException {
    private static final long serialVersionUID = 1L;

    /** Where the {@code unreachable} is written, where the code that reached it said. */
    private final transient @Nullable Site site;

    /**
     * Where an {@code unreachable} stands in the source: the module whose text it is written in,
     * and the line and column it is at there, both counted from one.
     */
    public record Site(String module, int line, int column) {}

    /**
     * @param module the module whose text the {@code unreachable} is written in, or none where the
     *               code that reached it had no place for it
     * @param line   the line it is written at in that text, from one; nought where it has no place
     * @param column the column it is written at, from one
     */
    public UnreachableReached(String message, @Nullable String module, int line, int column) {
        super(message);
        this.site = module != null && line > 0 ? new Site(module, line, column) : null;
    }

    /** Where the {@code unreachable} is written, or none where the code that reached it was not
     *  told. */
    public @Nullable Site site() {
        return site;
    }

    /**
     * Aborts with {@code message}, written at {@code line} and {@code column} of {@code module}'s
     * text. Declared to answer a value so the emitted code reads as an expression like any other —
     * the position it stands in has a value on the stack in every path the verifier walks, and
     * nothing follows it at run time. A {@code module} of none, or a line of nought, is an
     * {@code unreachable} the code generator had no place for, and the abort names none.
     */
    // Emitted code calls this, so it is not a method to keep callers away from: what it is for is
    // being reached.
    @SuppressWarnings("DoNotCallSuggester")
    public static Object reached(String message, @Nullable String module, int line, int column) {
        throw new UnreachableReached(message, module, line, column);
    }
}
