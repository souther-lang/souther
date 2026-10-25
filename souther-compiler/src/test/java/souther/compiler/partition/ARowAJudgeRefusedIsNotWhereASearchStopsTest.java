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
    void aWayThatBuiltNoRowIsNotHeldBack() {
        List<Generator.BoundaryAttempt> held = new ArrayList<>();
        Generator.BoundaryAttempt none = new Generator.BoundaryAttempt.Unresolved(
                new Generator.UnresolvedCombination(List.of("a rule of the decision"),
                        Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE),
                CompositionAccount.NOTHING);

        assertFalse(Generator.builtLeavingNothingOut(none, held));
        assertTrue(held.isEmpty());
    }

    @Test
    void aRefusedRowStandsOnlyWhereEveryWayUnderTheCasesWasTried() {
        assertTrue(Generator.aRefusedRowStands(
                ContentsAsked.UnderTheCases.Walked.EVERY_WAY_TRIED, SearchShortfall.NONE));
    }

    @Test
    void aRefusedRowDoesNotHideTheFigureThatEndedTheWalkOverTheCases() {
        SearchShortfall figure = SearchShortfall.of(CompositionShortfall.of(
                Set.of(CompositionBudget.WAYS_UNDER_THE_CASES_TRIED)));

        assertFalse(Generator.aRefusedRowStands(
                ContentsAsked.UnderTheCases.Walked.STOPPED_AT_THE_FIGURE, figure));
    }

    @Test
    void aRefusedRowDoesNotHideAWayUnderACaseNobodyRead() {
        assertFalse(Generator.aRefusedRowStands(
                ContentsAsked.UnderTheCases.Walked.EVERY_WAY_TRIED,
                SearchShortfall.NONE.unreadWhere(true)));
    }

    private static Generator.BoundaryAttempt built(boolean refused) {
        return new Generator.BoundaryAttempt.Built(new Generator.GeneratedRow(
                new Generator.Purpose.ForAPoint("a rule of the decision"), List.of()),
                CompositionAccount.NOTHING, refused);
    }
}
