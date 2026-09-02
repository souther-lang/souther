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
 * <p>A value and not the thing that gathered it. What a reader hands on is compared, held beside
 * other answers and carried into records that compare by their fields, so a mutable gathering handed
 * out under this name would be a value whose equality is identity and whose contents anyone holding
 * it may add to. The gathering is {@link Gathered}, which producers keep to themselves.
 *
 * <p><b>Whether the classification came out is said by whoever knows, and never read off the
 * reason.</b> A clause read far enough to be a bound on a number has its questions worked out and
 * its line unanswered, and a reason saying the reading stopped is true of it. Where a rule's
 * classification did not come out, what says so is the reading that classifies — which for a
 * declaration's clauses is {@code check.Required}, and for a body's comparison is that there is no
 * such reading at all.
 *
 * @param stated       what a report says about a rule that came to no line where it was filed, from
 *                     whichever of the two things happened to the reading. A rule the reading did
 *                     not finish is here as well wherever a reader is owed the sentence about it,
 *                     which is what the finding is for; what it leaves a measure is the question
 *                     beside it
 * @param unclassified the rules nothing worked out the questions of, each holding the measures it
 *                     leaves open
 */
public record RulesWithNoLine(List<RuleWithoutALine> stated,
                              List<StandingQuestion.Unclassified> unclassified) {

    /** Nothing found, which is what a reader with no rules to read hands on. */
    public static final RulesWithNoLine NONE = new RulesWithNoLine(List.of(), List.of());

    public RulesWithNoLine {
        stated = List.copyOf(stated);
        unclassified = List.copyOf(unclassified);
    }

    /** Both readers' answers, as one, each fact still once. */
    public RulesWithNoLine and(RulesWithNoLine other) {
        Gathered both = new Gathered();
        both.addAll(this);
        both.addAll(other);
        return both.found();
    }

    /**
     * What one reader gathers on its way through, each fact once and in the order it was first
     * found.
     *
     * <p>The one fold on these identities. Six readers find them, and a rule met by two is one
     * thing with both of their handles beside it — folded by each reader for itself, a rule cited
     * two ways came out cited whichever way was met first.
     */
    public static final class Gathered {

        private final Map<RuleWithoutALine.Fact, RuleWithoutALine> stated = new LinkedHashMap<>();
        private final Map<Object, StandingQuestion.Unclassified> unclassified = new LinkedHashMap<>();

        /** One more finding, which is what a report says about the rule at that place. */
        public void add(RuleRef rule, RuleCitation cited, FilingCoordinate at,
                        BlockReason.RuleWithoutLineReason why) {
            add(RuleWithoutALine.of(rule, cited, at, why));
        }

        /**
         * The same, from a reader whose rules nothing classifies.
         *
         * <p>A question and not a finding beside it. Both would be one thing said twice to one
         * reader: what a report is owed about such a rule is that nothing worked out what it states
         * here, which is what the question says. A body's comparison and a clause of an
         * {@code ensures} come this way — there is no reading that says what either raises, so
         * where the reading of one stopped there is nothing to have been determined.
         */
        public void unclassified(RuleRef rule, RuleCitation cited, FilingCoordinate at,
                                 BlockReason.RuleReadingStopped why) {
            asked(StandingQuestion.NothingClassifiesIt.of(rule, cited, at, why));
        }

        /**
         * A rule that was classified, one of whose questions this could not decide, and the finding
         * beside it.
         *
         * <p>Both, because they are two things about one rule and neither says the other. The
         * finding is what a report tells a reader about what became of the rule here; the question
         * is what holds the measure answering it open, and it names the question rather than
         * leaving a reader to work out which of them is undecided.
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

        /** Everything another reader handed on, kept apart the same way. */
        public void addAll(RulesWithNoLine other) {
            other.stated().forEach(this::add);
            other.unclassified().forEach(this::asked);
        }

        /** What this gathering came to, which is what a reader hands on. */
        public RulesWithNoLine found() {
            return new RulesWithNoLine(List.copyOf(stated.values()),
                    List.copyOf(unclassified.values()));
        }
    }
}
