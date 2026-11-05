package souther.compiler.inputs;

import souther.compiler.check.RuleCitation;
import souther.compiler.check.RuleRef;
import souther.compiler.check.RuleReportAnchor;
import souther.compiler.meaning.CaseExpansion;
import souther.compiler.types.ModelOccurrences;

import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * What a rule's line not worked out because its cases were too many was told of those cases, for
 * a report to say beside why the line was not worked out.
 *
 * <p>Beside the finding and not in it. The finding is why the line was not worked out, and two of
 * them about one rule at one place are put together as one; a count of one case of one line is
 * put together with nothing, since the ways of one case are none of another's. So this is its own
 * entry, about the rule and the line, and a report joins the two by the rule.
 *
 * @param rule      which rule of the model
 * @param reachedBy every question a reader was offered for the rule, as a finding about it holds
 *                  ({@link RuleWithoutALine#reachedBy})
 * @param readAt    every copy of the model's code the rule was read at with these cases
 * @param expansion the line, the case of it, how many ways it was, and what made its parts
 */
public record CasesExpandedAtARule(RuleRef rule, Set<RuleReportAnchor> reachedBy,
                                   ModelOccurrences readAt, CaseExpansion expansion) {

    public CasesExpandedAtARule {
        Objects.requireNonNull(rule, "cases are a rule's");
        Objects.requireNonNull(readAt, "a rule is read at some copies, if only none");
        Objects.requireNonNull(expansion, "and were some number of ways");
        reachedBy = reachedBy == null ? Set.of() : Set.copyOf(reachedBy);
        RuleCitation.requireReached(rule, reachedBy);
    }

    /** One reader's account of it, read at {@code readAt}. */
    public static CasesExpandedAtARule of(RuleCitation cited, ModelOccurrences readAt,
                                          CaseExpansion expansion) {
        return new CasesExpandedAtARule(cited.rule(), RuleCitation.anchorOf(cited), readAt,
                expansion);
    }

    /**
     * What makes two of these one: the rule, and which case of which of its lines this is and what
     * it came to, wherever read. The case is told apart as the reading told it apart, by the
     * line's relation and the condition the case was said as, so two cases coming to the same are
     * two of these.
     */
    public Object key() {
        return List.of(rule, expansion);
    }

    /** How a reader finds the rule. */
    public Set<RuleCitation> cited() {
        return RuleCitation.handlesFor(rule, reachedBy);
    }

    /** Two accounts of one rule's cases as one: every handle and every copy either was read at. */
    public CasesExpandedAtARule mergedWith(CasesExpandedAtARule other) {
        if (!key().equals(other.key())) {
            throw new IllegalArgumentException("two accounts put together are of one rule's"
                    + " cases: " + this + " and " + other);
        }
        Set<RuleReportAnchor> both = new HashSet<>(reachedBy);
        both.addAll(other.reachedBy);
        return new CasesExpandedAtARule(rule, both, readAt.and(other.readAt), expansion);
    }
}
