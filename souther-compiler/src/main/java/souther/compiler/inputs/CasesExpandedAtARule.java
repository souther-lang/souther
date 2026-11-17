package souther.compiler.inputs;

import souther.compiler.check.RuleCitation;
import souther.compiler.check.RuleRef;
import souther.compiler.check.RuleReportAnchor;
import souther.compiler.meaning.CaseExpansion;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.ModelOccurrences;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * What a rule's line not worked out because its cases were too many was told of one of those
 * cases, for a report to say beside why the line was not worked out.
 *
 * <p>Beside the finding and not in it. The finding is why the line was not worked out, and two of
 * them about one rule at one place are put together as one; a count of one case of one line is
 * put together with nothing, since the ways of one case are none of another's. So this is its own
 * entry, about the rule and the case, and a report joins the two by the rule.
 *
 * <p>One entry for each case of each line of the rule, and nothing else tells two apart
 * ({@link #key}). A comparison written in a helper is one rule read once per call, and each
 * reading answers what the case came to there: the counts, and what in that copy of the model made
 * the parts. Those answers are kept as readings of the one case, each with the copies it was read
 * at, and never numbered as cases of their own. Readings that came to the same are one reading
 * read at each of their copies; one copy reads a case once, so a copy answered two ways is two of
 * this compiler's answers disagreeing, and is raised.
 *
 * @param rule      which rule of the model
 * @param reachedBy every question a reader was offered for the rule, as a finding about it holds
 *                  ({@link RuleWithoutALine#reachedBy})
 * @param which     which case of which of its lines
 * @param line      the quantity the line is on, as a report names it
 * @param cutAt     where on the quantity the line is
 * @param readings  what the case came to, each answer with every copy it was read at, in the
 *                  order they were first read
 */
public record CasesExpandedAtARule(RuleRef rule, Set<RuleReportAnchor> reachedBy,
                                   CaseExpansion.Which which, String line, String cutAt,
                                   List<Reading> readings) {

    public CasesExpandedAtARule {
        Objects.requireNonNull(rule, "cases are a rule's");
        Objects.requireNonNull(which, "some case of some line");
        Objects.requireNonNull(line, "cases are a line's");
        Objects.requireNonNull(cutAt, "a line is somewhere on its quantity");
        reachedBy = reachedBy == null ? Set.of() : Set.copyOf(reachedBy);
        readings = List.copyOf(readings);
        RuleCitation.requireReached(rule, reachedBy);
        if (readings.isEmpty()) {
            throw new IllegalArgumentException("a case told of was read somewhere: " + which);
        }
        Set<ModelOccurrence> seen = new HashSet<>();
        for (Reading each : readings) {
            for (ModelOccurrence copy : each.readAt()) {
                if (!seen.add(copy)) {
                    throw new IllegalStateException("one copy of " + rule + " answered what "
                            + which + " came to two ways, at " + copy);
                }
            }
        }
    }

    /**
     * What one case came to, read at {@code readAt}.
     *
     * @param readAt every copy of the model's code it was read at with this answer
     * @param cameTo the answer
     */
    public record Reading(ModelOccurrences readAt, CaseExpansion.CameTo cameTo) {

        public Reading {
            Objects.requireNonNull(readAt, "a reading is made at some copies, if only none");
            Objects.requireNonNull(cameTo, "and came to something");
        }
    }

    /** What makes two of these one: the rule, and which case of which of its lines. */
    public record Key(RuleRef rule, CaseExpansion.Which which) {}

    /** Which line of which rule, which is what its cases are numbered among. */
    public record LineOfARule(RuleRef rule, CaseExpansion.Line line) {}

    /** One reader's account of it, read at {@code readAt}. */
    public static CasesExpandedAtARule of(RuleCitation cited, ModelOccurrences readAt,
                                          CaseExpansion expansion) {
        return new CasesExpandedAtARule(cited.rule(), RuleCitation.anchorOf(cited),
                expansion.which(), expansion.line(), expansion.cutAt(),
                List.of(new Reading(readAt, expansion.cameTo())));
    }

    /** What makes two of these one. */
    public Key key() {
        return new Key(rule, which);
    }

    /** Which line of which rule this is a case of. */
    public LineOfARule lineOfTheRule() {
        return new LineOfARule(rule, which.line());
    }

    /** How a reader finds the rule. */
    public Set<RuleCitation> cited() {
        return RuleCitation.handlesFor(rule, reachedBy);
    }

    /**
     * Two accounts of one case as one: every handle either was reached by, and every reading
     * either made — a reading that came to what one already did is that one, read at more copies.
     */
    public CasesExpandedAtARule mergedWith(CasesExpandedAtARule other) {
        if (!key().equals(other.key())) {
            throw new IllegalArgumentException("two accounts put together are of one case: "
                    + this + " and " + other);
        }
        // One place of one line is named one way, since its name is read off the place.
        if (!line.equals(other.line) || !cutAt.equals(other.cutAt)) {
            throw new IllegalStateException("one place of a line named two ways: " + line + " at "
                    + cutAt + " and " + other.line + " at " + other.cutAt);
        }
        Set<RuleReportAnchor> both = new HashSet<>(reachedBy);
        both.addAll(other.reachedBy);
        List<Reading> all = new ArrayList<>(readings);
        for (Reading more : other.readings) {
            int at = indexOf(all, more.cameTo());
            if (at < 0) {
                all.add(more);
            } else {
                all.set(at, new Reading(all.get(at).readAt().and(more.readAt()), more.cameTo()));
            }
        }
        return new CasesExpandedAtARule(rule, both, which, line, cutAt, all);
    }

    private static int indexOf(List<Reading> readings, CaseExpansion.CameTo cameTo) {
        for (int at = 0; at < readings.size(); at++) {
            if (readings.get(at).cameTo().equals(cameTo)) {
                return at;
            }
        }
        return -1;
    }
}
