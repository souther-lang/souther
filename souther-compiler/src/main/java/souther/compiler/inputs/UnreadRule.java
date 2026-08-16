package souther.compiler.inputs;

/**
 * A position a rule is written about that this did not turn into a line, and what stopped it.
 *
 * <p>Asked of the rule and not of the position. One position carries more than one statement, and a
 * line read at it says nothing about the rest — a threshold on {@code x} does not answer for the
 * bound beside it that nothing could read.
 *
 * <p><b>Whichever rule drew it.</b> A {@code guard}'s comparison and a newtype's invariant are two
 * producers of one kind of evidence (spec §example-partition), so a reader of this list is told the
 * same thing about either and does not have to know which wrote it. Named after the guard while only
 * guards produced one, an invariant nothing could read had nowhere to be said and was dropped in
 * silence — the position then came back as one the model divides no way, which is the opposite of
 * what the declaration says.
 *
 * @param at  the position, spelled the way a report names it
 * @param why what would have to change before this rule could be a line, in this compiler's own
 *            terms. Which word a report writes for it is {@link ReportedReason}'s, so a capability
 *            gained here need not move a published vocabulary
 */
public record UnreadRule(TermPath at, BlockReason why) {}
