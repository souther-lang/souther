package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.UnheldNumber;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * An edge that offered no value says what it was short of, in every vocabulary it was short in.
 *
 * <p>An edge falls short of everything there is in more than one way — a figure of this compiler's
 * refused a candidate, a population this compiler writes some of ran out, a number it worked out
 * could not be held — and only the first is a number anybody could raise. Whichever it was, the
 * point is open on this compiler and not on the model.
 *
 * <p><b>Put to the one place that decides it.</b> A caller that worked the arm out by asking one of
 * the vocabularies whether it was empty is a caller that has to be taught every vocabulary there
 * will ever be. The one that existed before a population was a vocabulary asked about figures
 * alone, and the one after it asked about figures and populations: an edge short only of a number
 * it could not hold came back as a search that simply found nothing. Nothing at the model's end saw
 * the difference, because the word is the same word either way — which is why this is asked here
 * rather than through a model.
 */
class AnEdgeThatOfferedNothingSaysEverythingItIsShortOfTest {

    private static final String LABEL = "List.sum(q.xs) = 7";

    private static final CompositionCapacity A_SHARE_NOT_HELD = new CompositionCapacity(
            CompositionCapacity.Where.VALUES_A_TOTAL_IS_SPREAD_OVER,
            UnheldNumber.NO_REPRESENTATION_EXISTS);

    /** A figure refused a candidate, and the same walk wrote some of a population and could not
     *  hold a number. */
    @Test
    void anEdgeAFigureStoppedSaysTheFigureAndEverythingElseItMet() {
        CompositionShortfall met = CompositionShortfall.of(
                Set.of(CompositionBudget.WAYS_DOWN_TO_A_TOTAL_TRIED),
                Set.of(CompositionRepertoire.WAYS_A_TOTAL_IS_SPREAD), Set.of(A_SHARE_NOT_HELD));

        Generator.BoundaryAttempt.Stopped stopped = assertInstanceOf(
                Generator.BoundaryAttempt.Stopped.class, cameToNothing(met),
                "a figure refused a candidate, which is the outcome that names something to raise");
        assertEquals(met, stopped.met(),
                "and it carries the figure and what the same walk met besides, which the figure"
                        + " does not make untrue and nothing else downstream would ever hear about");
    }

    /**
     * No figure refused anything, and the walk went to the end of what this compiler writes.
     *
     * <p>There is nothing to raise, so an outcome naming a figure would be a lie and an outcome
     * naming nothing would leave a reader free to conclude that every value was refused.
     */
    @Test
    void anEdgeShortOnlyOfAPopulationSaysThePopulation() {
        CompositionShortfall met =
                CompositionShortfall.writing(Set.of(CompositionRepertoire.WAYS_A_TOTAL_IS_SPREAD));

        Generator.BoundaryAttempt.Unexhausted some = assertInstanceOf(
                Generator.BoundaryAttempt.Unexhausted.class, cameToNothing(met),
                "nothing was refused, so this is not a search a figure stopped");
        assertEquals(met, some.met(), "and what it is open on is what this compiler writes some of");
    }

    /** No figure refused anything and every population was walked, but a number could not be
     *  held: the point is open on a wider run, and says so. */
    @Test
    void anEdgeShortOnlyOfANumberItCouldNotHoldSaysTheNumber() {
        CompositionShortfall met = CompositionShortfall.of(Set.of(), Set.of(),
                Set.of(A_SHARE_NOT_HELD));

        Generator.BoundaryAttempt.Unexhausted some = assertInstanceOf(
                Generator.BoundaryAttempt.Unexhausted.class, cameToNothing(met),
                "a number this could not hold leaves the point open, never answered");
        assertEquals(met, some.met(), "and which number that was travels with it");
    }

    /** And an edge short of nothing is a search that had everything and came to nothing. */
    @Test
    void anEdgeShortOfNothingIsASearchThatHadEverything() {
        assertInstanceOf(Generator.BoundaryAttempt.Unresolved.class,
                cameToNothing(CompositionShortfall.NONE),
                "nothing of this compiler's is why, so nothing here may name one");
    }

    /** An edge that offered nothing and was short of {@code met}, as the outcome it comes to. */
    private static Generator.BoundaryAttempt cameToNothing(CompositionShortfall met) {
        return new Generator.Edge(realization(met), null)
                .cameToNothing(LABEL, CompositionAccount.NOTHING);
    }

    /** What such a walk came back with, which is the arm what it met puts it in. */
    private static TermRealizations.Realization realization(CompositionShortfall met) {
        if (!met.figures().isEmpty()) {
            return new TermRealizations.Realization.Stopped(met);
        }
        if (!met.nothing()) {
            return new TermRealizations.Realization.Unexhausted(met, null);
        }
        return new TermRealizations.Realization.None(
                Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
    }
}
