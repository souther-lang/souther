package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row built is not a row reached. A walk held to the run of its rows comes back with the first
 * row the judge refused where it reached none it accepts, and a search that walks on past one
 * attempt to the next way of composing does not stop at that.
 *
 * <p>Asked of the one place the ways of composing are walked, with attempts made by hand: which
 * way came back with a row is what these say, and not what the rows ran to.
 */
class ARowAJudgeRefusedIsNotWhereASearchStopsTest {

    @Test
    void aRowBuiltWholeAndAcceptedIsWhereTheWaysStop() {
        List<Generator.BoundaryAttempt> held = new ArrayList<>();

        assertTrue(Generator.builtLeavingNothingOut(built(false), held));
        assertTrue(held.isEmpty());
    }

    @Test
    void aRowBuiltWholeAndRefusedIsHeldBackAndTheWaysGoOn() {
        List<Generator.BoundaryAttempt> held = new ArrayList<>();
        Generator.BoundaryAttempt refused = built(true);

        assertFalse(Generator.builtLeavingNothingOut(refused, held));
        assertSame(refused, held.getFirst(), "it stands where no way reaches a row");
    }

    @Test
    void aWayThatLookedAtEveryCandidateAndBuiltNoRowIsNotHeldBack() {
        List<Generator.BoundaryAttempt> held = new ArrayList<>();

        assertFalse(Generator.builtLeavingNothingOut(
                unresolved(Generator.UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED), held));
        assertTrue(held.isEmpty());
    }

    /**
     * An {@code Unresolved} is a word, and a word may say candidates were not all looked at: it is
     * held back beside a row refused as a search a figure stopped is, and what each word says is
     * the word's, not read off the shape that carries it.
     */
    @Test
    void aWayWhoseWordSaysCandidatesWereNotAllLookedAtIsHeldBackBesideARowRefused() {
        List<Generator.BoundaryAttempt> held = new ArrayList<>();
        Generator.BoundaryAttempt untried = unresolved(
                Generator.UnresolvedCombination.Reason.NOT_ALL_CANDIDATES_COULD_BE_OFFERED);
        Generator.BoundaryAttempt complete = unresolved(
                Generator.UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED);

        assertFalse(Generator.builtLeavingNothingOut(built(true), held));
        assertFalse(Generator.builtLeavingNothingOut(untried, held));

        assertSame(untried, Generator.heldBack(held, complete));
    }

    @Test
    void aWordProvingNothingCanStandThereLookedAtEverything() {
        for (Generator.UnresolvedCombination.Reason each
                : Generator.UnresolvedCombination.Reason.values()) {
            if (each.provesInfeasible()) {
                assertFalse(each.leavesSomethingUntried(), each::name);
            }
        }
    }

    private static Generator.BoundaryAttempt unresolved(
            Generator.UnresolvedCombination.Reason reason) {
        return new Generator.BoundaryAttempt.Unresolved(
                new Generator.UnresolvedCombination(List.of("a rule of the decision"), reason),
                CompositionAccount.NOTHING);
    }

    @Test
    void aRefusedRowStandsOnlyWhereEveryWayUnderTheCasesWasTried() {
        assertTrue(Generator.aRefusedRowStands(
                ContentsAsked.UnderTheCases.Walked.EVERY_WAY_TRIED, SearchShortfall.NONE, false));
    }

    /**
     * A way under a case whose parameter's search was cut by a figure is a way the walk over the
     * cases did finish, and what that search found out is not the walk's: the row refused does not
     * stand over it.
     */
    @Test
    void aRefusedRowDoesNotHideAParameterWhoseSearchWasNotLookedAtWhole() {
        assertFalse(Generator.aRefusedRowStands(
                ContentsAsked.UnderTheCases.Walked.EVERY_WAY_TRIED, SearchShortfall.NONE, true));
    }

    @Test
    void aSearchAFigureStoppedIsHeldBackBesideTheRowsRefused() {
        List<Generator.BoundaryAttempt> held = new ArrayList<>();
        Generator.BoundaryAttempt stopped = Generator.BoundaryAttempt.Unplanned.at(
                "a rule of the decision", Set.of(CompositionBudget.WAYS_UNDER_THE_CASES_TRIED),
                CompositionAccount.NOTHING);
        // Held back beside the row, whichever of them was reached first.

        assertFalse(Generator.builtLeavingNothingOut(built(true), held));
        assertFalse(Generator.builtLeavingNothingOut(stopped, held));

        assertSame(stopped, Generator.heldBack(held,
                        unresolved(Generator.UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED)),
                "a row refused does not stand in the place of a search that was stopped");
    }


    @Test
    void aRefusedRowDoesNotHideTheFigureThatEndedTheWalkOverTheCases() {
        SearchShortfall figure = SearchShortfall.of(CompositionShortfall.of(
                Set.of(CompositionBudget.WAYS_UNDER_THE_CASES_TRIED)));

        assertFalse(Generator.aRefusedRowStands(
                ContentsAsked.UnderTheCases.Walked.STOPPED_AT_THE_FIGURE, figure, false));
    }

    @Test
    void aRefusedRowDoesNotHideAWayUnderACaseNobodyRead() {
        assertFalse(Generator.aRefusedRowStands(
                ContentsAsked.UnderTheCases.Walked.EVERY_WAY_TRIED,
                SearchShortfall.NONE.unreadWhere(true), false));
    }

    private static Generator.BoundaryAttempt built(boolean refused) {
        return new Generator.BoundaryAttempt.Built(new Generator.GeneratedRow(
                new Generator.Purpose.ForAPoint("a rule of the decision"), List.of()),
                CompositionAccount.NOTHING, refused);
    }
}
