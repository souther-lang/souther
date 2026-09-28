package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.UnheldNumber;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A number a candidate could not hold travels with every answer built from that candidate, and is
 * never read as nothing having been there to build.
 *
 * <p>A search that tries several numbers and builds at none of them answers with what all of them
 * met. Kept as a figure and a population and nothing else, a candidate that was short only of a
 * number it could not hold contributed nothing to either, and the search came back as one that
 * composed nothing for a reason about the model — the confusion {@code ExactAnswer} exists to keep
 * a caller from making, at the one place several answers are joined into one.
 */
class ANumberNoCandidateCouldHoldTravelsWithTheSearchesAnswerTest {

    private static final CompositionCapacity A_SHARE_NOT_HELD = new CompositionCapacity(
            CompositionCapacity.Where.VALUES_A_TOTAL_IS_SPREAD_OVER,
            UnheldNumber.NO_REPRESENTATION_EXISTS);

    private static final CompositionShortfall ONLY_UNHELD =
            CompositionShortfall.of(Set.of(), Set.of(), Set.of(A_SHARE_NOT_HELD));

    @Test
    void aCandidateShortOnlyOfANumberLeavesTheWalkUnexhaustedRatherThanNothingComposed() {
        TermRealizations.Realization came = TermRealizations.firstThatBuilds(true,
                TermRealizations.Tried.allOf(List.of(Count.of(1))),
                (Place _) -> new TermRealizations.Realization.Unexhausted(ONLY_UNHELD, null));

        TermRealizations.Realization.Unexhausted some = assertInstanceOf(
                TermRealizations.Realization.Unexhausted.class, came,
                "a number the candidate could not hold leaves the search open, not answered");
        assertEquals(ONLY_UNHELD, some.met(), "and it says which number that was");
    }

    /** And beside a figure another candidate met, the number is not lost to the stop. */
    @Test
    void aNumberOneCandidateCouldNotHoldTravelsBesideAFigureAnotherMet() {
        CompositionShortfall stoppedHere =
                CompositionShortfall.of(Set.of(CompositionBudget.WAYS_DOWN_TO_A_TOTAL_TRIED));
        TermRealizations.Realization came = TermRealizations.firstThatBuilds(true,
                TermRealizations.Tried.allOf(List.of(Count.of(1), Count.of(2))),
                (Place at) -> ((Count) at).at().intValue() == 1
                        ? new TermRealizations.Realization.Unexhausted(ONLY_UNHELD, null)
                        : new TermRealizations.Realization.Stopped(stoppedHere));

        TermRealizations.Realization.Stopped stopped = assertInstanceOf(
                TermRealizations.Realization.Stopped.class, came,
                "a figure met is what names something to raise");
        assertEquals(stoppedHere.and(ONLY_UNHELD), stopped.met(),
                "and the number the other candidate could not hold is carried beside it");
    }

    /** A class nothing reached for over a number it could not hold says so, and is no crash. */
    @Test
    void aClassUnreachedOverANumberItCouldNotHoldIsARepresentativeNotArrivedAt() {
        RepresentativeSource.NotArrivedAt source = assertDoesNotThrow(
                () -> new RepresentativeSource.NotArrivedAt(ONLY_UNHELD, "nothing here composed"),
                "a number this could not hold is what stopped the reaching, and is said");
        assertEquals(ONLY_UNHELD, source.met());
    }
}
