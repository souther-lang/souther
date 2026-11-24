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
 * What a rule's line was told of one of its cases, for a report to say beside the line: what the
 * case came to when the line was not worked out because its cases were too many
 * ({@code CasesAtARule<CaseExpansion.CameTo>}), or the helpers its choices stand among when the
 * line was read all the same ({@code CasesAtARule<List<CaseExpansion.MultipliedHelper>>}). The two
 * are kept in lists of their own, since a line read at a cost has no count and no reason it was not
 * read; what they share is how accounts of one case are put together, and that is held here once.
 *
 * <p>Beside the finding and not in it. The finding is why the line was not worked out, and two of
 * them about one rule at one place are put together as one; an account of one case of one line is
 * put together with nothing, since the ways of one case are none of another's. So this is its own
 * entry, about the rule and the case, and a report joins the two by the rule.
 *
 * <p>One entry for each case of each line of the rule, and nothing else tells two apart
 * ({@link #key}). A comparison written in a helper is one rule read once per call, and each
 * reading answers what the case came to there. Those answers are kept as readings of the one case,
 * each with the copies it was read at, and never numbered as cases of their own. Readings that came
 * to the same are one reading read at each of their copies; one copy reads a case once, so a copy
 * answered two ways is two of this compiler's answers disagreeing, and is raised.
 *
 * @param <A>       what a reading of a case answers
 * @param rule      which rule of the model
 * @param reachedBy every question a reader was offered for the rule, as a finding about it holds
 *                  ({@link RuleWithoutALine#reachedBy})
 * @param which     which case of which of its lines
 * @param line      the quantity the line is on, as a report names it
 * @param cutAt     where on the quantity the line is
 * @param readings  what the case came to, each answer with every copy it was read at, in the
 *                  order they were first read
 */
public record CasesAtARule<A>(RuleRef rule, Set<RuleReportAnchor> reachedBy,
                              CaseExpansion.Which which, String line, String cutAt,
                              List<Reading<A>> readings) {

    public CasesAtARule {
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
        for (Reading<A> each : readings) {
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
     * @param answer the answer
     */
    public record Reading<A>(ModelOccurrences readAt, A answer) {

        public Reading {
            Objects.requireNonNull(readAt, "a reading is made at some copies, if only none");
            Objects.requireNonNull(answer, "and came to something");
        }
    }

    /** What makes two of these one: the rule, and which case of which of its lines. */
    public record Key(RuleRef rule, CaseExpansion.Which which) {}

    /** Which line of which rule, which is what its cases are numbered among. */
    public record LineOfARule(RuleRef rule, CaseExpansion.Line line) {}

    /** One reader's account of {@code which}, read at {@code readAt}. */
    public static <A> CasesAtARule<A> of(RuleCitation cited, ModelOccurrences readAt,
                                         CaseExpansion.Which which, String line, String cutAt,
                                         A answer) {
        return new CasesAtARule<>(cited.rule(), RuleCitation.anchorOf(cited), which, line, cutAt,
                List.of(new Reading<>(readAt, answer)));
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
    public CasesAtARule<A> mergedWith(CasesAtARule<A> other) {
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
        List<Reading<A>> all = new ArrayList<>(readings);
        for (Reading<A> more : other.readings) {
            int at = indexOf(all, more.answer());
            if (at < 0) {
                all.add(more);
            } else {
                all.set(at, new Reading<>(all.get(at).readAt().and(more.readAt()), more.answer()));
            }
        }
        return new CasesAtARule<>(rule, both, which, line, cutAt, all);
    }

    private static <A> int indexOf(List<Reading<A>> readings, A answer) {
        for (int at = 0; at < readings.size(); at++) {
            if (readings.get(at).answer().equals(answer)) {
                return at;
            }
        }
        return -1;
    }
}
