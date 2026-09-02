package souther.compiler.inputs;

import souther.compiler.check.CoverageObligation;
import souther.compiler.check.RuleCitation;
import souther.compiler.check.RuleRef;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What the readers found about the rules that came to no line here, and the rules among them
 * nothing worked out the questions of.
 *
 * <p>One entry point for six readers. A reader hands over the rule, the place it was filed at and
 * its own account of why there is no line here, and that is a finding about the rule at that place
 * — what a report says, whichever of the two things happened to the reading.
 *
 * <p><b>Whether the classification came out is said separately and by whoever knows.</b> It is not
 * read back off the reason: a clause read far enough to be a bound on a number has its questions
 * worked out and its line unanswered, and a reason saying the reading stopped is true of it. Where
 * a rule's classification did not come out, what says so is the reading that classifies — which for
 * a declaration's clauses is {@code check.Required} and for a body's comparison is that there is no
 * such reading at all.
 *
 * <p>Each fact once, and in the order it was first found. A rule met by two readers is one thing
 * with both of their handles beside it; which order a document puts them in is that document's.
 */
public final class RulesWithNoLine {

    private final Map<RuleWithoutALine.Fact, RuleWithoutALine> stated = new LinkedHashMap<>();
    private final Map<Object, StandingQuestion.Unclassified> unclassified = new LinkedHashMap<>();

    public RulesWithNoLine() {
    }

    /** One more finding, which is what a report says about the rule at that place. */
    public void add(RuleRef rule, RuleCitation cited, FilingCoordinate at,
                    BlockReason.RuleWithoutLineReason why) {
        add(RuleWithoutALine.of(rule, cited, at, why));
    }

    /**
     * The same, from a reader whose rules nothing classifies.
     *
     * <p>A question and not a finding beside it. Both would be one thing said twice to one reader:
     * what a report is owed about such a rule is that nothing worked out what it states here, which
     * is what the question says. A comparison is what comes this way — there is no reading that
     * says what one raises, so where the reading of it stopped there is nothing to have been
     * determined.
     */
    public void unclassified(RuleRef rule, RuleCitation cited, FilingCoordinate at,
                             BlockReason.RuleReadingStopped why) {
        asked(StandingQuestion.NothingClassifiesIt.of(rule, cited, at, why));
    }

    /**
     * A rule that was classified, one of whose questions this could not decide, and the finding
     * beside it.
     *
     * <p>Both, because they are two things about one rule and neither says the other. The finding
     * is what a report tells a reader about what became of the rule here; the question is what
     * holds the measure answering it open, and it names the question rather than leaving a reader
     * to work out which of them is undecided.
     */
    public void undetermined(RuleRef rule, RuleCitation cited, FilingCoordinate at,
                             CoverageObligation which,
                             BlockReason.RuleReadingStopped why) {
        add(RuleWithoutALine.of(rule, cited, at, why));
        asked(StandingQuestion.ObligationUndetermined.of(rule, cited, at, which, why));
    }

    /** One a reader already made, which is how the findings of two readings meet. */
    public void add(RuleWithoutALine one) {
        stated.merge(one.fact(), one, RuleWithoutALine::mergedWith);
    }

    /** The same, for a rule nothing worked out what it raises. */
    public void asked(StandingQuestion.Unclassified one) {
        unclassified.merge(one.fact(), one,
                (had, more) -> (StandingQuestion.Unclassified) had.mergedWith(more));
    }

    public void addAll(List<RuleWithoutALine> some) {
        some.forEach(this::add);
    }

    /** Everything another reader found, kept apart the same way. */
    public void addAll(RulesWithNoLine other) {
        other.stated.values().forEach(this::add);
        other.unclassified.values().forEach(this::asked);
    }

    /** The rules this compiler read to the end that draw no line where they were filed. */
    public List<RuleWithoutALine> stated() {
        return List.copyOf(stated.values());
    }

    /** The rules it did not read far enough to say what they raise. */
    public List<StandingQuestion.Unclassified> unclassified() {
        return List.copyOf(unclassified.values());
    }
}
