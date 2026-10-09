package souther.compiler.semantics;

/**
 * Which argument of an operation is the closure it applies, which parameter of that closure the
 * value arrives on, which argument holds the values it comes from, and which parameter the key a
 * map files the value under arrives on.
 *
 * <p>Numbers about one operation, which is what "hands its closure the contents of" comes to when
 * it is said in argument positions. It is a description of the operation and belongs here; how it is
 * arrived at — reading the library's own signature — is the frontend's and belongs there
 * ({@link souther.compiler.check.Combinators}).
 *
 * <p>The numbers are positions of the operation's arguments, so one is meaningful only beside a
 * call to that operation. Nothing here reads them; they are read where an {@link ArgumentRef} is
 * resolved.
 *
 * @param keyParam the closure parameter the key arrives on, or {@link #NO_KEY} where the closure is
 *                 handed none — the container is not a map, or the closure takes the value alone
 * @param applied  how far the operation goes applying the closure
 */
public record Combinator(int closureArg, int elementParam, int containerArg, int keyParam,
                         HowAClosureIsApplied applied) {

    public Combinator {
        if (applied == null) {
            throw new IllegalArgumentException("an operation applies its closure some way");
        }
    }

    /** No parameter of the closure is handed a key. */
    public static final int NO_KEY = -1;

    /** Whether the closure is handed the key the value is filed under. */
    public boolean handsAKey() {
        return keyParam != NO_KEY;
    }
}
