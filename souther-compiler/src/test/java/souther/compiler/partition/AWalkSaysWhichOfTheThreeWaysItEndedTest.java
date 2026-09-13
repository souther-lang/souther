package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Text;

import java.math.BigDecimal;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * How a walk outward ended, which is not one question with two answers.
 *
 * <p>A walk may end having tried every place there was; it may end at a figure somebody wrote down,
 * with a place the run holds left untaken; and it may end because the order has no step to take,
 * where the one place it started from is the whole of what it can name and what else the run holds
 * is not something it walked.
 *
 * <p><b>The last two are both limits and are not the same limit.</b> A figure is a number to raise
 * and raising it goes past; an order with no step is reached by no number at all. A caller handed
 * one for the other is sent to raise something that had already run to its end, or told that
 * nothing would have helped where a figure would. So they are told apart here, where the walk knows,
 * and not worked out afterwards from a count of what came back.
 */
class AWalkSaysWhichOfTheThreeWaysItEndedTest {

    /**
     * A run of strings that is one string has been walked entirely.
     *
     * <p>The order still has no step, and there is nothing further for a step to reach: both ends
     * are the place in hand and both of them its own. Said the other way, this would report a set
     * this compiler writes some of against a walk that wrote every member of it.
     */
    @Test
    void aRunOfOneStringWasWalkedEntirely() {
        assertEquals(Outwards.Ended.HAVING_TRIED_THEM_ALL,
                walkOfStrings(Endpoint.inclusive(Text.of("x")), Endpoint.inclusive(Text.of("x"))));
    }

    /**
     * A run of strings wider than the place in hand was not.
     *
     * <p>Every string has a next one, so a run reaching past this place holds others — and this
     * names none of them. Which is the limit the pair search reports rather than coming back as
     * though the rules left nothing.
     */
    @Test
    void aWiderRunOfStringsWasNot() {
        assertEquals(Outwards.Ended.WITH_NO_STEP_TO_TAKE, walkOfStrings(null, null));
        assertEquals(Outwards.Ended.WITH_NO_STEP_TO_TAKE,
                walkOfStrings(Endpoint.inclusive(Text.of("x")), Endpoint.inclusive(Text.of("y"))));
        // One end the run stops short of is enough, since what is asked is whether the run is the
        // place in hand and a run that does not hold one of its ends is not.
        assertEquals(Outwards.Ended.WITH_NO_STEP_TO_TAKE,
                walkOfStrings(Endpoint.exclusive(Text.of("a")), Endpoint.inclusive(Text.of("x"))));
    }

    /**
     * An order whose values step says which of the other two, and never this one.
     *
     * <p>The negative control the two above need. A walk that ended at the figure and a walk that
     * ended having tried them all are both walks of an order with a step, and a check that only
     * ever saw the third would pass with the other two collapsed into each other.
     */
    @Test
    void anOrderWithAStepEndsTheOtherTwoWays() {
        assertEquals(Outwards.Ended.HAVING_TRIED_THEM_ALL,
                walkOfCounts(between("0", "3"), 8));
        assertEquals(Outwards.Ended.AT_THE_FIGURE,
                walkOfCounts(between("0", "100"), 4));
    }

    /**
     * A walk stopped by the figure may not come back saying what a walk with no step says.
     *
     * <p>Which is what the two vocabularies being apart comes to downstream, and it is refused
     * rather than left to whoever assembles the answer. A caller that worked out which of the two it
     * had from whether every place was tried had one word for both — a figure met and an order with
     * no step are alike in that, and alike in nothing else.
     */
    @Test
    void aWalkStoppedByTheFigureDoesNotSpeakForAWalkWithNoStep() {
        assertThrows(IllegalArgumentException.class,
                () -> Realization.Unknown.searchLeftSomethingUntried(
                        java.util.Set.of(CompositionBudget.PLACES_A_PAIR_IS_TRIED_AT),
                        java.util.Set.of(
                                CompositionRepertoire.PLACES_A_PAIR_IS_TRIED_AT_ON_A_LINE)));
        // And the population travels on its own, which is what a walk with no step hands over.
        assertEquals(java.util.Set.of(CompositionRepertoire.PLACES_A_PAIR_IS_TRIED_AT_ON_A_LINE),
                Realization.Unknown.searchLeftSomethingUntried(java.util.Set.of(),
                        java.util.Set.of(
                                CompositionRepertoire.PLACES_A_PAIR_IS_TRIED_AT_ON_A_LINE))
                        .notAllOf());
    }

    private static Outwards.Ended walkOfStrings(Endpoint low, Endpoint high) {
        return Outwards.from(Text.of("x"), Count.of(1), Carrier.TEXT,
                new NumericDomain.Bounds(low, high), 8).ended();
    }

    private static Outwards.Ended walkOfCounts(NumericDomain.Bounds within, int howMany) {
        return Outwards.from(Count.of(BigDecimal.ZERO), Count.of(1),
                new Carrier.Whole(), within, howMany).ended();
    }

    private static NumericDomain.Bounds between(String low, String high) {
        return new NumericDomain.Bounds(
                Endpoint.inclusive(Count.of(new BigDecimal(low))),
                Endpoint.inclusive(Count.of(new BigDecimal(high))));
    }
}
