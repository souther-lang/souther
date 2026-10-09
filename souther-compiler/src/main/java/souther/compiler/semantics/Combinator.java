package souther.compiler.semantics;

/**
 * Which argument of an operation is the closure it applies, which parameter of that closure the
 * value arrives on, which argument holds the values it comes from, which parameter the key a map
 * files the value under arrives on — and that the operation does apply it, and how far.
 *
 * <p>Numbers about one operation, which is what "hands its closure the contents of" comes to when
 * it is said in argument positions. Where the arguments are is read off the operation's signature;
 * that the closure is applied to them, and how far, is read off its body or declared of a kernel
 * ({@code check.Combinators}). A signature alone says a closure could be handed an element, and
 * never that it is.
 *
 * <p>The numbers are positions of the operation's arguments, so one is meaningful only beside a
 * call to that operation. Nothing here reads them; they are read where an {@link ArgumentRef} is
 * resolved.
 *
 * @param keyParam   the closure parameter the key arrives on, or {@link #NO_KEY} where the closure
 *                   is handed none — the container is not a map, or the closure takes the value
 *                   alone
 * @param applied    how far the operation goes applying the closure
 * @param startsFrom the argument holding the index of the first element the closure is handed, or
 *                   {@link #FROM_THE_FIRST} where it is handed them from the first. What is said of
 *                   a call of an operation with such an argument holds only where the argument is
 *                   nought
 */
public record Combinator(int closureArg, int elementParam, int containerArg, int keyParam,
                         HowAClosureIsApplied applied, int startsFrom) {

    public Combinator {
        if (applied == null) {
            throw new IllegalArgumentException("an operation applies its closure some way");
        }
    }

    /** No parameter of the closure is handed a key. */
    public static final int NO_KEY = -1;

    /** The closure is handed the container's elements from the first. */
    public static final int FROM_THE_FIRST = -1;

    /** Whether the closure is handed the key the value is filed under. */
    public boolean handsAKey() {
        return keyParam != NO_KEY;
    }

    /** Where the arguments are, which is all a signature says. */
    public ClosurePositions positions() {
        return new ClosurePositions(closureArg, elementParam, containerArg, keyParam);
    }
}
