package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The numbers tried for several totals at once are the choices of one number for each, and what
 * is left over is every reason the searches that handed the numbers over stopped, with the
 * reason the choices themselves were cut: a reader raising one figure is told about the others.
 */
class TheNumbersOfSeveralTotalsKeepEveryReasonTheirSearchesStoppedTest {

    private static TermRealizations.Tried searchedAs(TermRealizations.Remainder rest,
                                                     int... numbers) {
        List<Place> out = new ArrayList<>();
        for (int each : numbers) {
            out.add(Count.of(each));
        }
        return new TermRealizations.Tried(out, rest);
    }

    private static final TermRealizations.Remainder NAMED_ONLY = new TermRealizations.Remainder
            .SomeOf(Set.of(CompositionRepertoire.PLACES_IN_A_RUN_THAT_ARE_NAMED));

    private static final TermRealizations.Remainder CUT = new TermRealizations.Remainder
            .StoppedAt(CompositionBudget.VALUES_OF_AN_UNBOUNDED_PROGRESSION_TRIED);

    /**
     * One total whose numbers are the ones this names and another whose search was cut at a
     * figure: the figure alone would tell a reader that raising it reaches everything.
     */
    @Test
    void aPopulationOfOneTotalAndAFigureOfAnotherAreBothSaid() {
        TermRealizations.Together together = TermRealizations.Together.of(List.of(
                searchedAs(NAMED_ONLY, 100), searchedAs(CUT, 5)));

        assertEquals(List.of(List.of(Count.of(100), Count.of(5))), together.each());
        assertTrue(together.rest().populations()
                        .contains(CompositionRepertoire.PLACES_IN_A_RUN_THAT_ARE_NAMED),
                () -> "the population the first total's numbers are a part of: "
                        + together.rest());
        assertTrue(together.rest().figures()
                        .contains(CompositionBudget.VALUES_OF_AN_UNBOUNDED_PROGRESSION_TRIED),
                () -> "the figure the second total's search was cut at: " + together.rest());
    }

    /** The order the totals are asked in does not choose which reason is kept. */
    @Test
    void theOrderOfTheTotalsDoesNotChooseWhichReasonIsKept() {
        TermRealizations.Together together = TermRealizations.Together.of(List.of(
                searchedAs(CUT, 5), searchedAs(NAMED_ONLY, 100)));

        assertTrue(together.rest().populations()
                .contains(CompositionRepertoire.PLACES_IN_A_RUN_THAT_ARE_NAMED),
                () -> "" + together.rest());
        assertTrue(together.rest().figures()
                .contains(CompositionBudget.VALUES_OF_AN_UNBOUNDED_PROGRESSION_TRIED),
                () -> "" + together.rest());
    }

    /**
     * More choices than the figure for them allows: the choices are cut at that figure and not at
     * the one that bounds the numbers of one total, and what the totals' own searches left is said
     * beside it.
     */
    @Test
    void choicesCutAtTheirOwnFigureSayItBesideWhatEachSearchLeft() {
        int most = CompositionBudget.COMBINATIONS_OF_TOTALS_TRIED.maximum();
        int[] many = new int[most];
        for (int i = 0; i < many.length; i++) {
            many[i] = i;
        }
        TermRealizations.Together together = TermRealizations.Together.of(List.of(
                searchedAs(NAMED_ONLY, many), searchedAs(NAMED_ONLY, 0, 1)));

        assertEquals(most, together.each().size(), "as many choices as the figure allows");
        assertTrue(together.rest().figures()
                        .contains(CompositionBudget.COMBINATIONS_OF_TOTALS_TRIED),
                () -> "the figure the choices were cut at: " + together.rest());
        assertTrue(together.rest().populations()
                        .contains(CompositionRepertoire.PLACES_IN_A_RUN_THAT_ARE_NAMED),
                () -> "and what the searches of the totals left: " + together.rest());
    }

    /**
     * Choices that fit the figure exactly are not cut: the figure is reached only where a choice
     * was left out.
     */
    @Test
    void choicesThatFitTheirFigureAreNotSaidToHaveBeenCut() {
        int most = CompositionBudget.COMBINATIONS_OF_TOTALS_TRIED.maximum();
        int[] first = new int[most];
        for (int i = 0; i < first.length; i++) {
            first[i] = i;
        }
        TermRealizations.Together together = TermRealizations.Together.of(List.of(
                searchedAs(new TermRealizations.Remainder.Exhausted(), first),
                searchedAs(new TermRealizations.Remainder.Exhausted(), 7)));

        assertEquals(most, together.each().size());
        assertTrue(together.rest().nothing(), () -> "" + together.rest());
    }
}
