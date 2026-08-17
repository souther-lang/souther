package souther.compiler.inputs;

/**
 * Why a position's declarations did not settle whether a distinction can stand there.
 *
 * <p>Two kinds, and telling them apart is the point. One is a reading that stopped: a rule was
 * written and this compiler could not take it in, so what the rules leave is wider than the rules
 * are. The other is a reading that finished and was then set aside, because acting on what it found
 * is a decision this compiler has not made yet.
 *
 * <p>Run together, the second reads as the first, and an author is told a rule went unread when
 * every rule was read and understood.
 */
public sealed interface Unsettlement {

    /** A rule about the position went unread, and it could refuse the distinction as readily as one
     *  that was read. */
    record ReadingStopped(BlockReason why) implements Unsettlement {

        public ReadingStopped {
            if (why == null) {
                throw new IllegalArgumentException("a reading stopped by nothing did not stop");
            }
        }
    }

    /**
     * The rules leave the position no value at all, and the declared distinctions were handed back
     * rather than acted on ({@link ObligationDomain.Reason#EMPTY_DOMAIN_POLICY_PENDING}).
     *
     * <p>So nothing may be concluded from the distinction being counted: it is there because the
     * reading was set aside, and not because anything admits it.
     */
    record RulesLeaveNothing() implements Unsettlement {}

    /**
     * The reading of this position states no such distinction.
     *
     * <p>Which is not a refusal. A refusal is a rule saying the position cannot hold a value; this
     * is two readings of the model not being about the same values, and the position has nothing to
     * say about one it never read.
     */
    record NoSuchDistinction() implements Unsettlement {}

}
