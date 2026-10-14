package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.CameToNothing;
import souther.compiler.partition.CompositionAccount;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.CompositionRepertoire;
import souther.compiler.partition.CompositionShortfall;
import souther.compiler.partition.Generator;

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
                                CompositionBudget.CHARACTERS_A_PROPOSAL_HOLDS))))),
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
                built.unrepresented()));
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

    private static Generator.BoundaryAttempt built() {
        return new Generator.BoundaryAttempt.Built(new Generator.GeneratedRow(
                new Generator.Purpose.ForAPoint("a rule of the decision"), List.of()),
                CompositionAccount.NOTHING);
    }
}
