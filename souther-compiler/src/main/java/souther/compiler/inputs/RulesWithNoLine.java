package souther.compiler.inputs;

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
 * @param reported     what a report says about a rule that came to no line where it was filed, from
 *                     whichever of the two things happened to the reading. A rule the reading did
 *                     not finish is here as well wherever a reader is owed the sentence about it,
 *                     which is what the finding is for; what it leaves a measure is the question
 *                     beside it. Named for the surface and not for the reading, because it is one
 *                     list for one reader — what the model states is {@link #modelStatements()},
 *                     asked of the reasons rather than read off this
 * @param unclassified the rules nothing worked out the questions of, each holding the measures it
 *                     leaves open
 */
public record RulesWithNoLine(List<RuleWithoutALine> reported,
                              List<StandingQuestion.Unclassified> unclassified) {

    /** Nothing found, which is what a reader with no rules to read hands on. */
    public static final RulesWithNoLine NONE = new RulesWithNoLine(List.of(), List.of());

    public RulesWithNoLine {
        reported = List.copyOf(reported);
        unclassified = List.copyOf(unclassified);
    }

    /**
     * The rules among them that this compiler read from end to end, which is the model stating
     * something at the place they were filed.
     *
     * <p>Its own answer beside {@link #reported()}, because they are different questions and only
     * one of them is about the model. What a report prints is every rule that came to no line here,
     * whichever of the two things happened to the reading; what a position's own account rests on
     * is whether the model said something there. Read off the report list, a rule this compiler
     * gave up on is counted as the model stating something — and a position waiting on a reading
     * comes back as one the model has spoken about.
     */
    public List<RuleWithoutALine> modelStatements() {
        return reported.stream()
                .filter(each -> each.why() instanceof BlockReason.ReadToEndWithoutLine)
                .toList();
    }

    /**
     * And the ones this compiler did not get through, which is the opposite sentence.
     *
     * <p>Beside {@link #unclassified()} rather than among them. A reader that files no finding for
     * such a rule leaves the question as the only thing saying the reading stopped; one whose
     * questions are raised by an accounting leaves the finding. Both are true of the same rule and
     * a caller asking whether a reading stopped here has to ask both, which is why neither list is
     * the whole answer and neither stands in for the other.
     */
    public List<RuleWithoutALine> readingsThatStopped() {
        return reported.stream()
                .filter(each -> each.why() instanceof BlockReason.RuleReadingStopped)
                .toList();
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

        private final Map<RuleWithoutALine.Fact, RuleWithoutALine> reported = new LinkedHashMap<>();
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
         * A rule that was classified and whose end this could not decide, and the finding beside
         * it.
         *
         * <p>Both, because they are two things about one rule and neither says the other. The
         * finding is what a report tells a reader about what became of the rule here; the question
         * is what holds the border measure open, and the classes are settled beside it rather than
         * held open with it.
         */
        public void boundaryUndetermined(RuleRef rule, RuleCitation cited, FilingCoordinate at,
                                         BlockReason.RuleReadingStopped why) {
            add(RuleWithoutALine.of(rule, cited, at, why));
            asked(StandingQuestion.BoundaryUndetermined.of(rule, cited, at, why));
        }

        /** One a reader already made, which is how the findings of two readings meet. */
        public void add(RuleWithoutALine one) {
            reported.merge(one.fact(), one, RuleWithoutALine::mergedWith);
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
            other.reported().forEach(this::add);
            other.unclassified().forEach(this::asked);
        }

        /** What this gathering came to, which is what a reader hands on. */
        public RulesWithNoLine found() {
            return new RulesWithNoLine(List.copyOf(reported.values()),
                    List.copyOf(unclassified.values()));
        }
    }
}
