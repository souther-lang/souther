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
 * What a rule's line that was read all the same, although its cases were more ways of choosing one
 * than are taken apart, was told of one of those cases: the helpers whose readings the case's
 * choices stand among one beside another, for a report to say where a model is dear to read.
 *
 * <p>Beside {@link CasesExpandedAtARule} and not among those, which say why a line was not worked
 * out and count the ways of a case. Nothing here is a count and no reason: a line read at a cost
 * is told of by the helper a model could declare as a behavior, and by nothing the numbers its
 * comparisons leave, which this does not hold.
 *
 * <p>One entry for each case of each line of the rule ({@link #key}). A comparison written in a
 * helper is one rule read once per call, and each copy answers which helpers its case chooses
 * among: the same answers are one reading read at each of their copies, and one copy answers
 * once.
 *
 * @param rule      which rule of the model
 * @param reachedBy every question a reader was offered for the rule, as a finding about it holds
 * @param which     which case of which of its lines
 * @param line      the quantity the line is on, as a report names it
 * @param cutAt     where on the quantity the line is
 * @param readings  the helpers the case chooses among, each answer with every copy it was read at,
 *                  in the order they were first read
 */
public record CasesReadAtACost(RuleRef rule, Set<RuleReportAnchor> reachedBy,
                               CaseExpansion.Which which, String line, String cutAt,
                               List<Reading> readings) {

    public CasesReadAtACost {
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
                    throw new IllegalStateException("one copy of " + rule + " answered which"
                            + " helpers " + which + " chooses among two ways, at " + copy);
                }
            }
        }
    }

    /**
     * The helpers one case chooses among, as read at {@code readAt}.
     *
     * @param readAt  every copy of the model's code it was read at with this answer
     * @param helpers the helpers whose readings the case's choices stand among
     */
    public record Reading(ModelOccurrences readAt, List<CaseExpansion.MultipliedHelper> helpers) {

        public Reading {
            Objects.requireNonNull(readAt, "a reading is made at some copies, if only none");
            helpers = List.copyOf(helpers);
            if (helpers.isEmpty()) {
                throw new IllegalArgumentException("a case is told of by the helpers it chooses"
                        + " among");
            }
        }
    }

    /** What makes two of these one: the rule, and which case of which of its lines. */
    public record Key(RuleRef rule, CaseExpansion.Which which) {}

    /** One reader's account of it, read at {@code readAt}. */
    public static CasesReadAtACost of(RuleCitation cited, ModelOccurrences readAt,
                                      CaseExpansion.CostlyCase told) {
        return new CasesReadAtACost(cited.rule(), RuleCitation.anchorOf(cited), told.which(),
                told.line(), told.cutAt(), List.of(new Reading(readAt, told.helpers())));
    }

    /** What makes two of these one. */
    public Key key() {
        return new Key(rule, which);
    }

    /** How a reader finds the rule. */
    public Set<RuleCitation> cited() {
        return RuleCitation.handlesFor(rule, reachedBy);
    }

    /**
     * Two accounts of one case as one: every handle either was reached by, and every reading
     * either made — a reading that came to the same helpers is that one, read at more copies.
     */
    public CasesReadAtACost mergedWith(CasesReadAtACost other) {
        if (!key().equals(other.key())) {
            throw new IllegalArgumentException("two accounts put together are of one case: "
                    + this + " and " + other);
        }
        if (!line.equals(other.line) || !cutAt.equals(other.cutAt)) {
            throw new IllegalStateException("one place of a line named two ways: " + line + " at "
                    + cutAt + " and " + other.line + " at " + other.cutAt);
        }
        Set<RuleReportAnchor> both = new HashSet<>(reachedBy);
        both.addAll(other.reachedBy);
        List<Reading> all = new ArrayList<>(readings);
        for (Reading more : other.readings) {
            int at = indexOf(all, more.helpers());
            if (at < 0) {
                all.add(more);
            } else {
                all.set(at, new Reading(all.get(at).readAt().and(more.readAt()), more.helpers()));
            }
        }
        return new CasesReadAtACost(rule, both, which, line, cutAt, all);
    }

    private static int indexOf(List<Reading> readings,
                               List<CaseExpansion.MultipliedHelper> helpers) {
        for (int at = 0; at < readings.size(); at++) {
            if (readings.get(at).helpers().equals(helpers)) {
                return at;
            }
        }
        return -1;
    }
}
