package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.PlacesApart;
import souther.compiler.numeric.Text;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;

import java.math.BigDecimal;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * How a walk outward ended, which is not one question with two answers.
 *
 * <p>A walk may end having tried every place there was; it may end having taken as many places as
 * it was asked for, with a place the run holds left untaken; it may end having walked past as many
 * places as it was allowed without taking that many; and it may end because the order has no step
 * to take, where the one place it started from is the whole of what it can name and what else the
 * run holds is not something it walked.
 *
 * <p><b>The last three are all limits and no two are the same limit.</b> A figure is a number to
 * raise and raising it goes past; an order with no step is reached by no number at all. A caller
 * handed one for the other is sent to raise something that had already run to its end, or told that
 * nothing would have helped where a figure would. So they are told apart here, where the walk knows,
 * and not worked out afterwards from a count of what came back.
 *
 * <p>And the two figures are two numbers. One is raised to try more of what the walk found, the
 * other to look further for something to find; they were one while every place the run held was a
 * place to take, and the narrowings a run has no word for are what separated them.
 */
class AWalkSaysWhichOfTheFourWaysItEndedTest {

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
        assertEquals(Outwards.Ended.AT_THE_FIGURE_OF_CANDIDATES,
                walkOfCounts(between("0", "100"), 4));
    }

    /**
     * The two figures are two, and a walk says which of them stopped it.
     *
     * <p>They were one number while every place the run held was a place to take. A narrowing the
     * run has no word for separates them: the walk may step past place after place and take none,
     * and what a reader raises to reach further is not what they raise to try more of what was
     * found. Reported as one, an author is sent to raise a number that changes nothing.
     */
    @Test
    void aWalkSaysWhichOfItsTwoFiguresStoppedIt() {
        // Every place of the run refused, so the taking never advances and the looking is what
        // runs out.
        assertEquals(Outwards.Ended.AT_THE_FIGURE_OF_PLACES_LOOKED_AT,
                Outwards.from(Count.of(BigDecimal.ZERO), Count.of(1), new Carrier.Whole(),
                        between("-100", "100"), 8, 5,
                        ValueSet.just(Value.number(0)), PlacesApart.NONE).ended());
        // And nothing refused, where the same walk runs out of candidates first.
        assertEquals(Outwards.Ended.AT_THE_FIGURE_OF_CANDIDATES,
                Outwards.from(Count.of(BigDecimal.ZERO), Count.of(1), new Carrier.Whole(),
                        between("-100", "100"), 4, 64,
                        ValueSet.ANY, PlacesApart.NONE).ended());
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

    /**
     * A place the run holds and a narrowing refuses is stepped past, not yielded, and is not the
     * run running out.
     *
     * <p>The three answers a walk gives are about the run. What the declarations leave a position
     * and what a rule holds it away from are not in the run, so a place either of them refuses is
     * one the walk goes through: yielded, it would be a candidate the rules refuse offered because
     * the run happened to hold it; read as the end of the run, everything past it would go
     * unwalked and the walk would say it had tried them all.
     */
    @Test
    void aPlaceANarrowingRefusesIsSteppedPastAndIsNotTheRunRunningOut() {
        Outwards.Walked walked = Outwards.from(Count.of(BigDecimal.ZERO), Count.of(1),
                new Carrier.Whole(), between("-3", "3"), 8, 64,
                ValueSet.ANY, PlacesApart.of(List.of(Count.of(1), Count.of(-1))));

        assertEquals(List.of(Count.of(0), Count.of(2), Count.of(-2), Count.of(3), Count.of(-3)),
                walked.places(),
                "the two places held apart are stepped past and the run beyond them is walked");
        assertEquals(Outwards.Ended.HAVING_TRIED_THEM_ALL, walked.ended(),
                "and the run still ran out, which is what the ending is about");
    }

    /** And the same for the set, which is the other narrowing a run has no word for. */
    @Test
    void aValueTheDeclarationsRefuseIsSteppedPastTheSameWay() {
        Outwards.Walked walked = Outwards.from(Count.of(BigDecimal.ZERO), Count.of(1),
                new Carrier.Whole(), between("-2", "2"), 8, 64,
                ValueSet.allBut(Value.number(1)), PlacesApart.NONE);

        assertEquals(List.of(Count.of(0), Count.of(-1), Count.of(2), Count.of(-2)),
                walked.places(),
                "the value the declarations refuse is not offered, and the rest of the run is");
    }

    private static Outwards.Ended walkOfStrings(Endpoint low, Endpoint high) {
        return Outwards.from(Text.of("x"), Count.of(1), Carrier.TEXT,
                new NumericDomain.Bounds(low, high), 8, 64, ValueSet.ANY,
                PlacesApart.NONE).ended();
    }

    private static Outwards.Ended walkOfCounts(NumericDomain.Bounds within, int howMany) {
        return Outwards.from(Count.of(BigDecimal.ZERO), Count.of(1),
                new Carrier.Whole(), within, howMany, 1024, ValueSet.ANY,
                PlacesApart.NONE).ended();
    }

    private static NumericDomain.Bounds between(String low, String high) {
        return new NumericDomain.Bounds(
                Endpoint.inclusive(Count.of(new BigDecimal(low))),
                Endpoint.inclusive(Count.of(new BigDecimal(high))));
    }
}
