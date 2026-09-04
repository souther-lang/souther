package souther.compiler.values;

/**
 * One place in a model somebody wrote, as something that can be carried past what knows what a model
 * is.
 *
 * <p>What is held is that two of these are the same place or are not, and nothing else. A reading
 * that asks a machine to be made knows which written thing asked; what makes the machine knows only
 * that a machine was asked for. Between them the question is which authored thing to send a reader
 * to, and the answer travels as one of these rather than being worked out again at the far end —
 * where the only thing left to work it out from is the position, and naming a position is not asking
 * for a machine.
 *
 * <p><b>Identity and no content.</b> There is nothing to compare but the thing itself: no equality
 * over what it stands for, because two places written the same way are two places, and no number,
 * because a number brings a question about what it is stable across and who hands them out. What
 * this is stable across is one compile, which is as far as anything asks.
 *
 * <p>Made where the places are already told apart. This says two of them are two; which two there
 * are is a fact about a model, and the reading that holds the model is what answers it — one of
 * these per authored thing, and the same one every time that thing is read.
 */
public final class AuthoredOccurrence {

    /**
     * Another place, told from every other by being this one.
     *
     * <p>Called once per authored thing and not once per reading of one. A caller that made one on
     * every visit would be handing out a token for having looked, and two readings of one clause
     * would be two places nobody wrote.
     */
    public static AuthoredOccurrence another() {
        return new AuthoredOccurrence();
    }

    private AuthoredOccurrence() {}

    @Override
    public String toString() {
        return "occurrence@" + Integer.toHexString(System.identityHashCode(this));
    }
}
