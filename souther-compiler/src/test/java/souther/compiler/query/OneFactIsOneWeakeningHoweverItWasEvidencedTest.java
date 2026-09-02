package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleCitation;
import souther.compiler.check.RuleRef;
import souther.compiler.diag.Citation;
import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.InputQuestion;
import souther.compiler.inputs.RuleWithoutALine;
import souther.compiler.inputs.StandingQuestion;
import souther.compiler.inputs.TermPath;
import souther.compiler.observe.Incompleteness;
import souther.compiler.partition.ClosureGap;
import souther.compiler.types.CoverageConstruct;
import souther.compiler.types.CoverageOrigin;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * What a measurement went without is a set of facts, and what tells two facts apart is what the
 * fact says it is.
 *
 * <p>Three of the arms hold more than the fact. An observation carries where it was said, a rule
 * with no line carries the handle an author is sent to, and a question that stands carries both
 * that handle and what each part of it was short of — and every one of those is declared, at the
 * type that holds it, to be no part of what tells one from another. A rule this compiler could not
 * read, met from two behaviors and cited at whichever place each of them was reading, is one thing
 * to tell a person.
 *
 * <p>So the union folds on the fact and never on the value. Folded on the value, a set that says
 * it holds each fact once holds one of them twice, and everything that counts what it holds counts
 * the paths a fact arrived by: a verdict names the same thing twice, and whichever of the two the
 * walk met first decides which place a reader is sent to.
 *
 * <p>And the evidence is kept. A fold that answered the count by taking one of the two and dropping
 * the other would be the same loss the other way round — the fact would be one, and where it was
 * met would be wherever the walk got to first.
 */
class OneFactIsOneWeakeningHoweverItWasEvidencedTest {

    @Test
    void anObservationMetAtTwoPlacesIsOneFact() {
        WeakeningSet here = observed(new SourcePos(1, 1));
        WeakeningSet there = observed(new SourcePos(2, 2));

        assertEquals(1, here.union(there).causes().size(),
                "one thing that was not observed, said of two places, is one fact");
        assertEquals(here.union(there), there.union(here),
                "which place was met first is no part of what the union comes to");
        // Neither side stands in for the union. A fold that kept one of the two would say the fact
        // once and say it was met only where the walk got to first.
        assertNotEquals(here, here.union(there),
                "a fact met at a second place is not the same value as one met at the first");
        assertEquals(Set.of(Citation.of(new SourcePos(1, 1)), Citation.of(new SourcePos(2, 2))),
                here.union(there).observationCauses().iterator().next().citations(),
                "and the one fact can send a reader to either place");
    }

    @Test
    void anObservationWithNoPlaceIsTheSameFactAsOneWithA() {
        WeakeningSet placed = observed(new SourcePos(1, 1));
        WeakeningSet unplaced = of(Weakening.ObservationIncomplete.of(
                Incompleteness.of(Incompleteness.Code.INSTRUMENTATION_ABSENT,
                        Incompleteness.Scope.MODULE, "m")));

        assertEquals(1, placed.union(unplaced).causes().size(),
                "an occurrence with nowhere to send a reader is the same fact as one with a place");
        assertEquals(Set.of(Citation.of(new SourcePos(1, 1))),
                placed.union(unplaced).observationCauses().iterator().next().citations(),
                "and the one that had nowhere to send a reader takes nothing away from the one"
                        + " that did");
    }

    @Test
    void aRuleCitedTwoWaysIsOneFact() {
        WeakeningSet named = ruleWithoutALine(new RuleCitation.Named("n"));
        WeakeningSet placed = ruleWithoutALine(
                new RuleCitation.WrittenAt(Citation.of(new SourcePos(3, 3))));

        assertEquals(1, named.union(placed).causes().size(),
                "a rule and the handle for it are two questions, and the union folds on the rule");
        assertEquals(named.union(placed), placed.union(named),
                "which reader cited it first is no part of what the union comes to");
        assertEquals(Set.of(new RuleCitation.Named("n"),
                        new RuleCitation.WrittenAt(Citation.of(new SourcePos(3, 3)))),
                ruleUnreadIn(named.union(placed)).cited(),
                "and the one rule keeps every handle a reader was offered");
    }

    @Test
    void aQuestionCitedTwoWaysIsOneFact() {
        WeakeningSet named = standingQuestion(new RuleCitation.Named("n"),
                List.of(new BlockReason.UnreadComparisonForm()));
        WeakeningSet placed = standingQuestion(
                new RuleCitation.WrittenAt(Citation.of(new SourcePos(3, 3))),
                List.of(new BlockReason.UnreadComparisonForm()));

        assertEquals(1, named.union(placed).causes().size(),
                "which rule it is and what it asks are what tell one standing question from"
                        + " another");
        assertEquals(Set.of(new RuleCitation.Named("n"),
                        new RuleCitation.WrittenAt(Citation.of(new SourcePos(3, 3)))),
                questionIn(named.union(placed)).cited(),
                "and the one question keeps every handle a reader was offered");
    }

    @Test
    void aQuestionShortOfTheSameTwoThingsIsOneFactWhicheverWasMetFirst() {
        BlockReason.AboutARule form = new BlockReason.UnreadComparisonForm();
        BlockReason.AboutARule none = new BlockReason.NoReadingTookItIn();
        RuleCitation named = new RuleCitation.Named("n");
        RuleCitation placed = new RuleCitation.WrittenAt(Citation.of(new SourcePos(3, 3)));
        WeakeningSet met = standingQuestion(named, List.of(form));
        WeakeningSet metElsewhere = standingQuestion(placed, List.of(none, form));

        assertEquals(1, met.union(metElsewhere).causes().size(),
                "what a question was short of is what it was short of, and not a sequence a reader"
                        + " of the parts arrived at");
        // Both of the things it carries beside the fact, joined in the one union. Written as two
        // folds a reader would have to ask which of them a merge had got round to.
        assertEquals(Set.of(form, none), questionIn(met.union(metElsewhere)).stopped(),
                "and every one of them is still there to be seen away");
        assertEquals(Set.of(named, placed), questionIn(met.union(metElsewhere)).cited(),
                "and both handles came with it");
    }

    /**
     * The laws, over the atoms this is about.
     *
     * <p>They hold of a set of Java values as well, which is why they said nothing while the atoms
     * were wrong. What they are worth is here: the atom is the fact, so three occurrences of one
     * fact come to one whichever way they are bracketed, and what evidenced each is all still there.
     */
    @Test
    void theUnionIsIdempotentCommutativeAndAssociativeOverFactsAndMergesTheirEvidence() {
        WeakeningSet here = observed(new SourcePos(1, 1));
        WeakeningSet there = observed(new SourcePos(2, 2));
        WeakeningSet elsewhere = observed(new SourcePos(3, 3));

        assertEquals(here, here.union(here), "a fact unioned with itself is the fact");
        assertEquals(here.union(there), there.union(here), "the order of two is no part of the sum");
        assertEquals(here.union(there).union(elsewhere), here.union(there.union(elsewhere)),
                "how three were bracketed is no part of the sum");
        assertEquals(1, here.union(there).union(elsewhere).causes().size(),
                "three occurrences of one fact are one fact");
        assertEquals(3, here.union(there).union(elsewhere)
                        .observationCauses().iterator().next().citations().size(),
                "and it was met at all three places");
    }

    /** The one rule this compiler stopped on, out of a set holding nothing else. */
    private static ClosureGap.RuleUnread ruleUnreadIn(WeakeningSet weakened) {
        return (ClosureGap.RuleUnread) modelReadingIn(weakened);
    }

    /** The one question that stands, out of a set holding nothing else. */
    private static ClosureGap.QuestionUnanswered questionIn(WeakeningSet weakened) {
        return (ClosureGap.QuestionUnanswered) modelReadingIn(weakened);
    }

    private static ClosureGap modelReadingIn(WeakeningSet weakened) {
        Weakening only = weakened.causes().iterator().next();
        return ((Weakening.ModelReadingIncomplete) only).cause();
    }

    private static WeakeningSet observed(SourcePos where) {
        return of(Weakening.ObservationIncomplete.of(
                Incompleteness.at(Incompleteness.Code.INSTRUMENTATION_ABSENT,
                        Incompleteness.Scope.MODULE, "m", where)));
    }

    private static WeakeningSet ruleWithoutALine(RuleCitation cited) {
        return of(new Weakening.ModelReadingIncomplete(ClosureGap.RuleUnread.of(
                new RuleWithoutALine(comparison(), cited,
                        new FilingCoordinate.AtPosition(TermPath.of("x")),
                        new BlockReason.UnreadComparisonForm()))));
    }

    private static WeakeningSet standingQuestion(RuleCitation cited,
                                                 List<BlockReason.AboutARule> stopped) {
        return of(new Weakening.ModelReadingIncomplete(ClosureGap.QuestionUnanswered.of(
                new StandingQuestion(comparison(), cited,
                        new InputQuestion.AboutAPosition(TermPath.of("x")), stopped))));
    }

    private static RuleRef comparison() {
        return new RuleRef.Comparison("b", new CoverageOrigin("m", 1, 1, CoverageConstruct.IF));
    }

    private static WeakeningSet of(Weakening one) {
        return WeakeningSet.of(one);
    }
}
