package souther.runtime;

import org.jspecify.annotations.Nullable;

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
    private static final long serialVersionUID = 1L;

    /** What broke, where it is a declared constraint; none for the other ends this class stands
     *  for, which have a message and no constraint (a division by zero, a number past its range). */
    private final transient @Nullable ConstraintFailure failure;

    /** Where the step that ended the run is written, where the generated code said; none
     *  otherwise. */
    private final transient @Nullable Site site;

    public ConstraintViolation(String message) {
        this(message, null, null);
    }

    private ConstraintViolation(String message, @Nullable ConstraintFailure failure,
                                @Nullable Site site) {
        super(message);
        this.failure = failure;
        this.site = site;
    }

    /**
     * Where a step stands in the source: the module whose text it is written in, and the line and
     * column it starts at, both counted from one.
     */
    public record Site(String module, int line, int column) {}

    /**
     * Where the step that ended the run is written: a refused construction, said by the code that
     * refused it, or an operation the language refuses to finish, said where the code was
     * generated to say it ({@link #placedAt}). None where the code that ended the run was not told
     * where it stands.
     */
    public @Nullable Site site() {
        return site;
    }

    /**
     * This, said to have ended the run at the step written at {@code line} and {@code column} of
     * {@code module}'s source — where it ended for an operation the language refuses to finish and
     * nothing has said where yet.
     *
     * <p>Where something has said, or this is a broken constraint, this as it is. A step inside the
     * one handed here said its own place first, as the run was leaving it, and that is the step the
     * run ended at; a constraint says its own place where it is refused. What generated code calls
     * where it was generated to say where each step that may end a run is written.
     */
    public ConstraintViolation placedAt(String module, int line, int column) {
        if (site != null || failure != null) {
            return this;
        }
        ConstraintViolation placed = new ConstraintViolation(String.valueOf(getMessage()), null,
                new Site(module, line, column));
        placed.setStackTrace(getStackTrace());
        return placed;
    }

    /**
     * The constraint that was broken, or none where this ends a run for some other reason.
     *
     * <p>The carrier is one class for every end that is a constraint of the language's, so the class
     * says that a run ended and not why. A caller that has to tell a broken invariant from a
     * division by zero asks here, and is not left to read the message.
     */
    public @Nullable ConstraintFailure failure() {
        return failure;
    }

    /**
     * The abort a broken constraint leaves by.
     *
     * <p>One entry and not one per origin. What a caller has is a failure that says what it is, so an
     * overload per kind would be this deciding again what the value already answers — and the day a
     * third origin is written, an overload it forgot would be an origin that aborts some other way.
     */
    public static ConstraintViolation notHeld(ConstraintFailure failure) {
        return new ConstraintViolation(failure.toString(), failure, null);
    }

    /**
     * Turns a construction result into a plain value or an abort: the constructed value when the
     * invariants held, or a thrown {@link ConstraintViolation} carrying the message when they did
     * not. Generated behavior bodies call this so a construction never surfaces a {@code Result}
     * on a public API and a violation never rides an output case.
     *
     * <p>Not a second way to abort. A construction's failure side is an {@link InvariantFailure} —
     * that is what {@code __construct} is typed to answer with — so what this has when it aborts is
     * a {@link ConstraintFailure}, and it leaves by {@link #notHeld} like any other. What is here
     * rather than there is the unwrapping: this is the boundary a {@code Result} stops at, and the
     * abort is what happens on one side of it.
     */
    public static Object orThrow(Result<?, ?> r) {
        return refused(r, null);
    }

    /**
     * The same, for a construction written at {@code line} and {@code column} of {@code module}'s
     * source: what a generated body calls, so the abort says which construction it was. A
     * {@code module} of none, or a line of nought, is a construction the code generator had no
     * place for, and the abort names none.
     */
    public static Object orThrow(Result<?, ?> r, @Nullable String module, int line, int column) {
        return refused(r, module != null && line > 0
                ? new Site(module, line, column) : null);
    }

    private static Object refused(Result<?, ?> r, @Nullable Site site) {
        if (r instanceof Result.Ok<?, ?> ok) {
            return ok.value();
        }
        Object failed = ((Result.Err<?, ?>) r).error();
        if (failed instanceof ConstraintFailure broken) {
            throw new ConstraintViolation(broken.toString(), broken, site);
        }
        // Nothing generated reaches here: the only results handed over are `__construct`'s. Said
        // rather than cast, because a cast would report a caller this was not written for as a
        // failure of the constraint it was asking about.
        throw new ConstraintViolation(String.valueOf(failed));
    }
}
