package souther.compiler.query;

/**
 * Where one arm stands in the account a report counts it in.
 *
 * <p>The one question a count, a finding, a mark on a page and a build's refusal all put to an arm:
 * is a row through it, is it owed one, or is it neither. Derived from the assessment and never held
 * beside it — asked of the evidence at each of those places instead, the four had four chances to
 * read one measurement differently, which is how a count and the arms named under it came to
 * disagree.
 *
 * <p>Beside {@link ObligationDisposition}, which answers for a point of a line. The two accounts
 * share the law that the difference between the numbers is walkable and share no vocabulary: what
 * takes a point out of the count is that nothing has shown a row can be written there, and what
 * takes an arm out is that the fork it belongs to stands for a number of rules nobody could
 * establish. Neither word means anything in the other account.
 */
public enum ArmDisposition {

    /** A row this compilation observed goes through the arm. */
    MET,

    /**
     * No row goes through it and every row was read.
     *
     * <p>The one state a finding is made of and a build can be told to refuse over.
     */
    UNMET,

    /**
     * No row was seen to go through it and a reading that could have been holding one did not run
     * to the end.
     *
     * <p>Counted and never a finding. Whether a row goes through the arm is what nobody can say, so
     * an author told to write one may be told to write one they have written; and left out of the
     * count, an arm the rows may already answer would go unsaid.
     */
    UNDECIDED,

    /** Outside the count, for a reason the arm carries ({@link ArmExclusion}). */
    NOT_COUNTED
}
