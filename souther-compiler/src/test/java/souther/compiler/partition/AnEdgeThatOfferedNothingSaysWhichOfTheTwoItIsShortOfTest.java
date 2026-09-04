package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * An edge that offered no value says what it was short of, in whichever vocabulary it was short in.
 *
 * <p>An edge falls short of everything there is in two ways — a figure of this compiler's refused a
 * candidate, and a population this compiler writes some of ran out — and only the first is a number
 * anybody could raise. Whichever it was, the point is open on this compiler and not on the model.
 *
 * <p><b>Put to the one place that decides it.</b> A caller that worked the arm out by asking one of
 * the two whether it was empty is a caller that has to be taught every vocabulary there will ever
 * be, and the one that existed before this was asked about figures alone: an edge short only of a
 * population came back as a search that simply found nothing, with what it had walked in part gone
 * before anything downstream could read it. Nothing at the model's end saw the difference, because
 * the word is the same word either way — which is why this is asked here rather than through a
 * model.
 */
class AnEdgeThatOfferedNothingSaysWhichOfTheTwoItIsShortOfTest {

    private static final String LABEL = "List.sum(q.xs) = 7";

    /** A figure refused a candidate, and the same walk had written some of a population. */
    @Test
    void anEdgeAFigureStoppedSaysTheFigureAndWhatItWalkedInPart() {
        Generator.BoundaryAttempt came = shortOf(
                Set.of(CompositionBudget.WAYS_DOWN_TO_A_TOTAL_TRIED),
                Set.of(CompositionRepertoire.WAYS_A_TOTAL_IS_SPREAD));

        Generator.BoundaryAttempt.Stopped stopped = assertInstanceOf(
                Generator.BoundaryAttempt.Stopped.class, came,
                "a figure refused a candidate, which is the outcome that names something to raise");
        assertEquals(Set.of(CompositionBudget.WAYS_DOWN_TO_A_TOTAL_TRIED), stopped.by(),
                "and it is the figure that refused one");
        assertEquals(Set.of(CompositionRepertoire.WAYS_A_TOTAL_IS_SPREAD), stopped.notAllOf(),
                "and what the same walk wrote some of, which the figure does not make untrue and"
                        + " which nothing else downstream would ever hear about");
    }

    /**
     * No figure refused anything, and the walk went to the end of what this compiler writes.
     *
     * <p>The one this got wrong. There is nothing to raise, so an outcome naming a figure would be
     * a lie and an outcome naming nothing would leave a reader free to conclude that every value
     * was refused.
     */
    @Test
    void anEdgeShortOnlyOfAPopulationSaysThePopulation() {
        Generator.BoundaryAttempt came =
                shortOf(Set.of(), Set.of(CompositionRepertoire.WAYS_A_TOTAL_IS_SPREAD));

        Generator.BoundaryAttempt.Unexhausted some = assertInstanceOf(
                Generator.BoundaryAttempt.Unexhausted.class, came,
                "nothing was refused, so this is not a search a figure stopped");
        assertEquals(Set.of(CompositionRepertoire.WAYS_A_TOTAL_IS_SPREAD), some.writes(),
                "and what it is open on is what this compiler writes some of");
    }

    /** And an edge short of neither is a search that had everything and came to nothing. */
    @Test
    void anEdgeShortOfNeitherIsASearchThatHadEverything() {
        Generator.BoundaryAttempt came = shortOf(Set.of(), Set.of());

        assertInstanceOf(Generator.BoundaryAttempt.Unresolved.class, came,
                "nothing of this compiler's is why, so nothing here may name one");
    }

    /** An edge that offered nothing and was short of these, as the outcome it comes to. */
    private static Generator.BoundaryAttempt shortOf(Set<CompositionBudget> stoppedBy,
                                                     Set<CompositionRepertoire> notAllOf) {
        return new Generator.Edge(realization(stoppedBy, notAllOf), null)
                .cameToNothing(LABEL, List.of());
    }

    /** What such a walk came back with, which is the arm its own two answers put it in. */
    private static TermRealizations.Realization realization(Set<CompositionBudget> stoppedBy,
                                                            Set<CompositionRepertoire> notAllOf) {
        if (!stoppedBy.isEmpty()) {
            return new TermRealizations.Realization.Stopped(stoppedBy, notAllOf);
        }
        if (!notAllOf.isEmpty()) {
            return new TermRealizations.Realization.Unexhausted(notAllOf, null);
        }
        return new TermRealizations.Realization.None(
                Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
    }
}
