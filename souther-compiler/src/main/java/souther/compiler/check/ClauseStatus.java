package souther.compiler.check;

/**
 * What the check proved about one clause where a value is built.
 *
 * <p>Three answers and not two. The invariant is the conjunction of its clauses, and what that
 * conjunction came out as is {@link InvariantChecker.Verdict} — a different question with a
 * different answer, asked of the construction rather than of a clause. A clause the values refute
 * and a clause nothing here settles are both clauses the guards did not establish, which is what
 * E2011 reports; only the first is a clause the value fails, which is what E2010 reports. One set
 * answering both is how E2010 came to say that a value is rejected by clauses that merely stand.
 *
 * <p>{@code UNKNOWN} is neither of the other two and not "not refuted": read that way it would hold
 * the established clauses as well.
 */
enum ClauseStatus {

    /** The guards establish it here. */
    SETTLED,

    /** Neither established nor refuted: what is known here does not decide it. */
    UNKNOWN,

    /** The value being built fails it. */
    REFUTED;

    /** Whether the guards left this clause standing, which is {@code UNKNOWN} and {@code REFUTED}
     * together — the question E2011 asks, and the one this enum refines rather than replaces. */
    boolean unsettled() {
        return this != SETTLED;
    }

    /**
     * What two readings of one clause found, together.
     *
     * <p>The greater of the two, on {@code SETTLED < UNKNOWN < REFUTED}: what one branch established
     * is not established where the other did not, and a value one branch refutes is a value refused
     * on a path that is reachable. Which is the same rule the two sets this refines were combined
     * by — union on one side, intersection on the other — written once, so that the order the
     * branches are read in cannot decide it.
     */
    static ClauseStatus of(ClauseStatus a, ClauseStatus b) {
        return a.compareTo(b) >= 0 ? a : b;
    }
}
