package souther.compiler.inputs;

import souther.compiler.check.RuleCitation;
import souther.compiler.check.RuleRef;

/**
 * One rule of the model, at one position it is about, that this did not turn into a line.
 *
 * <p>Asked of the rule, and it names one. One position carries more than one statement, and a line
 * read at it says nothing about the rest — a threshold on {@code x} does not answer for the bound
 * beside it that nothing could read. Carrying only the position, the sentence written from this
 * told an author that a rule about {@code r.cost} went unread and left them to find which rule; and
 * two rules stopped by one limit at one position came out as one line, which is what a finding
 * asked of the rule may not do.
 *
 * <p><b>Whichever rule drew it.</b> A {@code guard}'s comparison, a newtype's invariant and a
 * clause of an {@code ensures} are three producers of one kind of evidence (spec
 * §example-partition), so a reader of this list is told the same thing about any of them and does
 * not have to know which wrote it. Named after the guard while only guards produced one, an
 * invariant nothing could read had nowhere to be said and was dropped in silence — the position
 * then came back as one the model divides no way, which is the opposite of what the declaration
 * says.
 *
 * <p>Two values and not one, and for two reasons. {@code rule} tells one rule from another and is
 * what a reader groups by; {@code cited} is the handle an author acts on, and the two are not in
 * step wherever a rule has no name. Neither stands in for the other, and only the
 * first is part of what makes two of these one finding.
 *
 * @param rule  which rule of the model, as everything that names a rule names it
 * @param cited how a reader finds it — a name where the author gave one, a place where they did not
 * @param at    the position, spelled the way a report names it. One of these per position the rule
 *              is about: {@code a < b} leaves neither of them divided, and a reader looking up
 *              either is owed the same answer. Filed at the first alone, which position was named
 *              would turn on which side the author wrote it
 * @param why   what would have to change before this rule could be a line, in this compiler's own
 *              terms. Which word a report writes for it is {@link ReportedReason}'s, so a
 *              capability gained here need not move a published vocabulary
 */
public record UnreadRule(RuleRef rule, RuleCitation cited, Coordinate at,
                         BlockReason.AboutARule why) {

    public UnreadRule {
        if (rule == null || cited == null) {
            throw new IllegalArgumentException(
                    "a rule this could not read is one a reader can be sent to look at");
        }
        if (at == null || why == null) {
            throw new IllegalArgumentException("a rule went unread somewhere, and for something");
        }
    }

    /**
     * Which number of the position the reading was after when it stopped.
     *
     * <p>A position and not only a path. A {@code String} is measured two ways — its own order and
     * the length of it — and a rule about the length that nothing could read leaves the length
     * short and the string alone. Carried as a path, the two came back as one, and a report either
     * named the wrong one or fell short of both.
     *
     * <p><b>Where the reading was looking, and not what the rule is about.</b> What a rule this
     * could not read says about the position is exactly the part that was not read, so nothing here
     * may be promoted to the subject of an obligation: {@code a * a + b - b <= 9} is filed at both
     * positions, and the arithmetic that would have cancelled {@code b} is what stopped.
     *
     * <p>{@code measured} rather than the term itself, which is what the producers of these can
     * answer. An invariant's reading holds a path and whether it is a count, and the operation that
     * answered the count is not among what it kept — so a term here would be one this compiler made
     * up at the last moment for the shape of the type it is written in.
     *
     * @param path     where in the value it sits
     * @param measured whether it is a count taken of the position rather than the position's own
     *                 value
     */
    public record Coordinate(TermPath path, boolean measured) {

        public Coordinate {
            if (path == null) {
                throw new IllegalArgumentException("a reading stopped somewhere in the value");
            }
        }

        /** The position's own value, for a reading that was after it. */
        public static Coordinate at(TermPath path) {
            return new Coordinate(path, false);
        }

        @Override
        public String toString() {
            return measured ? "count of " + path : path.toString();
        }
    }

    /**
     * Whether this is the same finding as {@code other}.
     *
     * <p>The rule, the position and the limit. The citation is left out on purpose: a rule and the
     * handle for it are two questions, and a key holding the handle would file one rule under
     * several wherever the two come apart.
     */
    public boolean sameAs(UnreadRule other) {
        return rule.equals(other.rule) && at.equals(other.at) && why.equals(other.why);
    }
}
