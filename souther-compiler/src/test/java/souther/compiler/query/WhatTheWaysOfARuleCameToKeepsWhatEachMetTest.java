package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.partition.AnswersDemanded;
import souther.compiler.partition.CameToNothing;
import souther.compiler.partition.CompositionAccount;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.CompositionRepertoire;
import souther.compiler.partition.CompositionShortfall;
import souther.compiler.partition.ConditionOccurrence;
import souther.compiler.partition.ConditionReportAnchor;
import souther.compiler.partition.Generator;
import souther.compiler.partition.OnTheWay;
import souther.compiler.partition.ReachabilityGap;
import souther.compiler.partition.WayToTheBorder;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * What the ways of standing a rule's dependencies in came to, where none of them had a candidate to
 * try, is every one of them with what each met.
 *
 * <p>A rule is composed for once per way, and ways that had nothing to try are alike as an account
 * of the rule and not alike in what they met. Kept as the first of them, one figure an author could
 * raise was said and the other was dropped, and which of the two followed the order the ways were
 * enumerated in.
 *
 * <p>Put to the fold directly, the way the proof over the ways is
 * ({@link ARuleIsRefusedOnlyWhereEveryWayOfStandingItInProvesItTest}): what varies is the ways, and
 * a model that puts two standings under one rule varies in what the body reads as well.
 */
class WhatTheWaysOfARuleCameToKeepsWhatEachMetTest {

    /** Two ways that came back with one word, having met two figures, are one word having met both. */
    @Test
    void oneWordFromTwoWaysHoldsEveryFigureEitherMet() {
        Generator.BoundaryAttempt.NoRow elements =
                stoppedAt(CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS);
        RuleSettlement settled = cameTo(List.of(elements,
                stoppedAt(CompositionBudget.CHARACTERS_A_PROPOSAL_HOLDS)));

        assertEquals(List.of(RuleSearch.Came.of(new CameToNothing(elements.why(),
                        CompositionShortfall.of(Set.of(CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS,
                                CompositionBudget.CHARACTERS_A_PROPOSAL_HOLDS)), Set.of()))),
                settled.synthesisShortfalls(),
                "both figures are something an author could raise, so neither is dropped");
    }

    /** Two ways with two words are both said, each with what it met. */
    @Test
    void twoWordsFromTwoWaysAreBothSaid() {
        Generator.BoundaryAttempt.NoRow stopped =
                stoppedAt(CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS);
        Generator.BoundaryAttempt.NoRow unexhausted = writingSomeOf();

        assertEquals(Set.of(RuleSearch.Came.of(stopped.came()),
                        RuleSearch.Came.of(unexhausted.came())),
                Set.copyOf(cameTo(List.of(stopped, unexhausted)).synthesisShortfalls()),
                "a figure and a population walked in part are two things an author is told");
    }

    /**
     * Whichever order the ways were walked in, the rule's account is one value.
     *
     * <p>The pair and its mirror, for both shapes above. Read off the ways as they were met, a
     * model would say one thing and the same model with its dependencies listed the other way round
     * would say the other.
     */
    @Test
    void theOrderTheWaysWereWalkedInIsNotSaid() {
        Generator.BoundaryAttempt elements = stoppedAt(CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS);
        Generator.BoundaryAttempt characters =
                stoppedAt(CompositionBudget.CHARACTERS_A_PROPOSAL_HOLDS);
        Generator.BoundaryAttempt some = writingSomeOf();

        assertEquals(cameTo(List.of(elements, characters, some)),
                cameTo(List.of(some, characters, elements)),
                "which way a walk met first is not something the rule's account is a function of");
    }

    /**
     * And what the ways went without is what any of them went without, whichever was met first.
     *
     * <p>Two ways that came back with one word and went without two different conditions. One way's
     * account standing for both would leave the other condition unsaid, and which one was left out
     * would follow the order the ways were walked in.
     */
    @Test
    void whatEveryWayWentWithoutIsSaid() {
        Generator.BoundaryAttempt one = new Generator.BoundaryAttempt.Unresolved(
                nothingComposes(), CompositionAccount.ofTheInput(List.of(gap(0))));
        Generator.BoundaryAttempt other = new Generator.BoundaryAttempt.Unresolved(
                nothingComposes(), CompositionAccount.ofTheInput(List.of(gap(1))));

        assertEquals(List.of(gap(0), gap(1)), cameTo(List.of(other, one)).account().onTheWay(),
                "both conditions were gone without, in the order the reading states them");
        assertEquals(cameTo(List.of(one, other)), cameTo(List.of(other, one)),
                "whichever way was walked first, the rule's answer is one value");
    }

    /**
     * A search over a plan a figure cut short, or one nothing was planned for, did not stop at
     * the figure.
     *
     * <p>What it was handed was cut short, and that is held as itself: told it as a stop, a reader
     * goes looking for a search that did not finish.
     */
    @Test
    void aFigureThatCutThePlanShortIsNotAStop() {
        Set<CompositionBudget> plan = Set.of(CompositionBudget.DEPTH_A_CONSTRUCTION_PLAN_DESCENDS);
        Generator.BoundaryAttempt.NoRow limited = new Generator.BoundaryAttempt.Limited(
                nothingComposes(), plan, CompositionAccount.NOTHING);
        Generator.BoundaryAttempt.NoRow unplanned = new Generator.BoundaryAttempt.Unplanned(
                new Generator.UnresolvedCombination(List.of("a rule of the decision"),
                        Generator.UnresolvedCombination.Reason
                                .NO_READING_OF_THE_LINE_COULD_BE_SEARCHED),
                plan, CompositionAccount.NOTHING);

        for (Generator.BoundaryAttempt.NoRow each : List.of(limited, unplanned)) {
            assertEquals(CompositionShortfall.NONE, each.came().met(),
                    () -> "nothing stopped the search: " + each);
            assertEquals(plan, each.came().planCut(),
                    () -> "the figure cut short what it was handed: " + each);
        }
    }

    /** A way that had a row to try is the answer over every way that had none. */
    @Test
    void aWayWithARowToTryIsTheAnswer() {
        RuleSettlement settled = cameTo(List.of(
                stoppedAt(CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS), built()));

        assertInstanceOf(RuleRequirement.Unsettled.AComposedRowWentElsewhere.class,
                settled.requirement(),
                "a row was composed and run, which says more of the rule than nothing to try");
    }

    /** And no way at all is the classes not linking, and says so. */
    @Test
    void noWayAtAllIsTheClassesNotLinking() {
        assertEquals(List.of(RuleSearch.Came.of(CameToNothing.metNothing(
                        new Generator.UnresolvedCombination(List.of("a rule of the decision"),
                                Generator.UnresolvedCombination.Reason.LINKAGE_FAILED)))),
                cameTo(List.of()).synthesisShortfalls(),
                "nothing was tried, which is not a search that came to nothing");
    }

    private static RuleSettlement cameTo(List<Generator.BoundaryAttempt> ways) {
        return Adequacy.DecisionSearch.whatTheWaysCameTo(ways, built -> RuleSettlement.of(
                new RuleRequirement.Unsettled.AComposedRowWentElsewhere(),
                built.unrepresented()), new WayToTheBorder(List.of(declined(0), declined(1))),
                AnswersDemanded.NOTHING);
    }

    private static Generator.BoundaryAttempt.NoRow stoppedAt(CompositionBudget figure) {
        return new Generator.BoundaryAttempt.Stopped(new Generator.UnresolvedCombination(
                List.of("a rule of the decision"),
                Generator.UnresolvedCombination.Reason.wordFor(Set.of(figure))),
                CompositionShortfall.of(Set.of(figure)), CompositionAccount.NOTHING);
    }

    private static Generator.BoundaryAttempt.NoRow writingSomeOf() {
        return new Generator.BoundaryAttempt.Unexhausted(new Generator.UnresolvedCombination(
                List.of("a rule of the decision"),
                Generator.UnresolvedCombination.Reason.THE_SEARCH_LEFT_SOMETHING_UNTRIED),
                CompositionShortfall.writing(Set.of(CompositionRepertoire.WAYS_A_TOTAL_IS_SPREAD)),
                CompositionAccount.NOTHING);
    }

    private static Generator.UnresolvedCombination nothingComposes() {
        return new Generator.UnresolvedCombination(List.of("a rule of the decision"),
                Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
    }

    private static ReachabilityGap gap(int which) {
        return new ReachabilityGap.Unstated(declined(which));
    }

    private static OnTheWay.Declined declined(int which) {
        ConditionOccurrence condition =
                new ConditionOccurrence("f", ConditionOccurrence.Reading.DECIDING, which);
        return new OnTheWay.Declined(condition,
                new ConditionReportAnchor.WhereTheReadingMetIt("example.ruled", condition),
                new WhyNotTaken.OutsideDomain(WhyNotTaken.DomainLimit.A_QUANTITY_ON_NO_ORDER));
    }

    private static Generator.BoundaryAttempt built() {
        return new Generator.BoundaryAttempt.Built(new Generator.GeneratedRow(
                new Generator.Purpose.ForAPoint("a rule of the decision"), List.of()),
                CompositionAccount.NOTHING);
    }
}
