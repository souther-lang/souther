package souther.compiler.check;

/**
 * What the check proved about one clause where a value is built.
 *
 * <p>Three answers where one reading is being read, and not two. The invariant is the conjunction of
 * its clauses, and what that conjunction came out as is {@link InvariantChecker.Verdict} — a
 * different question with a different answer, asked of the construction rather than of a clause. A
 * clause the values refute and a clause nothing here settles are both clauses the guards did not
 * establish, which is what E2011 reports; only the first is a clause the value fails, which is what
 * E2010 reports. One set answering both is how E2010 came to say that a value is rejected by clauses
 * that merely stand.
 *
 * <p>{@code UNKNOWN} is neither of the others and not "not refuted": read that way it would hold the
 * established clauses as well.
 *
 * <p>The fourth is what a construction read on more than one path comes to. A conditional above a
 * construction is read once per branch, and the branches may fail different clauses: one refutes
 * this clause and establishes that one, the other the reverse. Every path then violates the
 * invariant — which is what E2010 is raised on — while no clause is one every path fails, and no
 * value that could be built here fails both. {@code REFUTED_SOMEWHERE} is that clause, kept apart
 * from {@code REFUTED} because "the value being built is one this clause rejects" is untrue of it.
 */
enum ClauseStatus {

    /** The guards establish it, on every path read. */
    SETTLED,

    /** Neither established nor refused: what is known does not decide it. */
    UNKNOWN,

    /** Refused on a path read here, and established or left undecided on another. Not a clause the
     * value fails: which of the clauses fails depends on which path the value comes down. */
    REFUTED_SOMEWHERE,

    /** The value being built fails it, on every path read. */
    REFUTED;

    /** Whether the guards left this clause standing, which is everything but {@code SETTLED} — the
     * question E2011 asks, and the one this enum refines rather than replaces. */
    boolean unsettled() {
        return this != SETTLED;
    }

    /** Whether a path was read on which the value fails this clause. */
    boolean refusedSomewhere() {
        return this == REFUTED || this == REFUTED_SOMEWHERE;
    }

    /**
     * What two readings of one clause found, together.
     *
     * <p>Where they agree, that; where they do not, the weaker of the two things that can be said,
     * which is what the disagreement leaves true. Two readings that established it establish it, and
     * two that refused it refuse it — a reading that establishes what another refuses leaves neither.
     *
     * <p>Not the greater of the two on a line through them. Reading it that way makes
     * {@code REFUTED} mean "refused on some path", which is what an invariant-level verdict is
     * decided by and is not what a clause-level one may say: E2010 reports the clauses a value fails,
     * and a value that fails this clause down one branch and that one down the other fails neither
     * wherever it is actually built.
     *
     * <p>Commutative, associative and idempotent, so the order the readings are combined in does not
     * decide what is reported.
     */
    static ClauseStatus of(ClauseStatus a, ClauseStatus b) {
        if (a == b) {
            return a;
        }
        return a.refusedSomewhere() || b.refusedSomewhere() ? REFUTED_SOMEWHERE : UNKNOWN;
    }

    /**
     * The same, against a reading that did not read this clause at all.
     *
     * <p>A clause one reading could not read there is a clause that reading established nothing
     * about, so what the other found holds of the paths it read and of no others. A refutation is
     * one of those: it says the value fails this clause where this reading looked, which is not the
     * same as failing it wherever it is built.
     *
     * <p>{@code SETTLED} answers itself here and no caller asks: a clause one reading established
     * and the other did not read is not established on every path either, and what becomes of it is
     * decided before this is reached — it is left out altogether, which is what the two sets this
     * refines did with it.
     */
    ClauseStatus whereTheOtherReadingSaysNothing() {
        return this == REFUTED ? REFUTED_SOMEWHERE : this;
    }
}
