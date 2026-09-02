package souther.compiler.inputs;

import souther.compiler.check.RuleCitation;
import souther.compiler.check.RuleRef;

import java.util.HashSet;
import java.util.Set;

/**
 * One rule of the model, at one position it is about, that this did not turn into a line.
 *
 * <p>Asked of the rule, and it names one. One position carries more than one statement, and a line
 * read at it says nothing about the rest — a threshold on {@code x} does not answer for the bound
 * beside it that nothing could read. Carrying only the position, the sentence written from this
 * told an author that a rule about {@code r.cost} went unread and left them to find which rule; and
 * two rules with no line at one position came out as one line, which is what a finding asked of the
 * rule may not do.
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
 * <p><b>Named for what is true of everything in it.</b> Two opposite things bring a rule here — one
 * this compiler got partway through, and one it read from end to end that draws no line — and what
 * they have in common is the whole of what this says: at this position, this rule is no line. Which
 * of the two it was is {@code why}, and it is asked of the type rather than read back out of a
 * word.
 *
 * <p><b>And neither of them is what holds a measure of coverage open.</b> That is a question about
 * a rule, which the reading that classifies the rule raises; this is what a report says about what
 * became of a rule here. Read as the first, a rule read completely was counted as one nobody could
 * read.
 *
 * @param fact  which rule, at which position, and why there is no line — the whole of what makes
 *              two of these one finding ({@link Fact})
 * @param cited how a reader finds it — a name where the author gave one, a place where they did
 *              not. Every one that was offered, because a rule found by two readers is one finding
 *              and each of them says how to reach it; which of them a document writes is that
 *              document's to decide
 */
public record RuleWithoutALine(Fact fact, Set<RuleCitation> cited) {

    public RuleWithoutALine {
        if (fact == null) {
            throw new IllegalArgumentException("a rule is without a line somewhere, and for a"
                    + " reason");
        }
        cited = cited == null ? Set.of() : Set.copyOf(cited);
        if (cited.isEmpty()) {
            throw new IllegalArgumentException(
                    "a rule with no line here is one a reader can be sent to look at");
        }
    }

    /** One reader's finding, as that reader produced it. */
    public static RuleWithoutALine of(RuleRef rule, RuleCitation cited, FilingCoordinate at,
                                      BlockReason.RuleWithoutLineReason why) {
        return new RuleWithoutALine(new Fact(rule, at, why), Set.of(cited));
    }

    /**
     * A rule with no line here, with the handle for it left out, which is the whole of what makes
     * two of them one.
     *
     * <p>The citation is no part of it. A rule and the handle for it are two questions, and a key
     * holding the handle files one rule under several wherever the two come apart — which they do
     * wherever a rule has no name of its own.
     */
    public record Fact(RuleRef rule, FilingCoordinate at, BlockReason.RuleWithoutLineReason why) {

        public Fact {
            if (rule == null || at == null || why == null) {
                throw new IllegalArgumentException("a rule is without a line somewhere, and for a"
                        + " reason");
            }
        }
    }

    /** Which rule of the model this is about. */
    public RuleRef rule() {
        return fact.rule();
    }

    /** The position it is about, spelled the way a report names it. */
    public FilingCoordinate at() {
        return fact.at();
    }

    /** Why there is no line here, in this compiler's own terms. */
    public BlockReason.RuleWithoutLineReason why() {
        return fact.why();
    }

    /**
     * Both readers' findings, as one: the rule, with every handle either of them offered.
     *
     * <p>Of one rule, and it says so rather than taking the caller's word. What comes out carries
     * this one's fact, so two that are not one fact would come out as one of them cited where the
     * other was.
     */
    public RuleWithoutALine mergedWith(RuleWithoutALine other) {
        if (!fact.equals(other.fact)) {
            throw new IllegalArgumentException("two findings put together are one rule with no"
                    + " line: " + fact + " and " + other.fact);
        }
        Set<RuleCitation> both = new HashSet<>(cited);
        both.addAll(other.cited);
        return new RuleWithoutALine(fact, both);
    }

}
