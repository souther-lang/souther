package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.check.Emptiness;
import souther.compiler.inputs.EmptyInput;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.PlacesApart;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.Text;
import souther.compiler.regex.PatternPlan;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;

import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * Where a position may stand is read off the run, the values the declarations leave, and the places
 * a rule holds it away from — all three, before a value is offered.
 *
 * <p>An order whose values step hides which of the three a search consulted: a candidate refused
 * after the fact costs a step, and the walk takes the next one. An order with no step has no next
 * one, so the first candidate is the only candidate and whichever of the three refuses it leaves the
 * position with nothing offered at all.
 *
 * <p>Two refusals and they are not one mechanism. A set the declarations leave is the model's answer
 * about the values a position holds; a place held away is a rule of the way this row has to take.
 * Written against one of them, a search would go on offering a value the other refuses — which is
 * why both are asked here, over the same order and the same run.
 */
class ACandidateOnAnOrderWithNoStepComesFromAllThreeThingsThatNarrowItTest {

    private static final NumericTerm.FromOnePosition NAME =
            new NumericTerm.ValueOf(TermPath.of("name"));

    /** The place a run open at both ends gives up on this order, which is the least string there
     *  is. Both refusals below are written at it, so that the fix is the only thing that moves. */
    private static final Place LEAST = Text.of("");

    /**
     * The declarations refuse the one place the run gives up, and a value is still offered.
     *
     * <p>A position whose rules leave it every string but the empty one — which is what a rule about
     * its length states — over a run nothing bounds. The run gives up the least string there is, the
     * set refuses exactly that, and an order with no step has nothing beside it: the value offered
     * has to come from the set rather than from the ends.
     */
    @Test
    void aSetTheDeclarationsLeaveNarrowsTheSearchAndNotWhatCameBackFromIt() {
        NumericWitness.Standing.Found stood = standing(
                new ARunWithHoles(NumericDomain.Bounds.OPEN, PlacesApart.NONE, null),
                ValueSet.allBut(Value.text("")));

        assertNotEquals(LEAST, stood.placeOf(NAME),
                "the declarations refuse the empty string, so it is not what is offered at the"
                        + " position");
    }

    /**
     * A rule holding the position away from the one place the run gives up, and a value is still
     * offered.
     *
     * <p>The other refusal over the same shape. Nothing narrows what the position holds; what takes
     * the place away is the way — a disequality, which leaves the run where it was and takes one
     * value out of it. Read off the run alone, the place offered is the one the hole is at and the
     * region refuses the row a step later.
     */
    @Test
    void aPlaceTheWayHoldsThePositionAwayFromIsNarrowedBySoNothingIsOfferedThere() {
        NumericWitness.Standing.Found stood = standing(
                new ARunWithHoles(NumericDomain.Bounds.OPEN, PlacesApart.of(List.of(LEAST)), null),
                ValueSet.ANY);

        assertNotEquals(LEAST, stood.placeOf(NAME),
                "the way holds the position away from the empty string, so it is not what is"
                        + " offered at it");
    }

    /**
     * And the run is still what the value is inside, which is what says the other two narrow the
     * search rather than replace it.
     *
     * <p>A control: without it, a search that ignored the run entirely would pass both tests above
     * by offering whatever the set or the machine happened to name first.
     */
    @Test
    void andTheValueOfferedIsOneTheRunHolds() {
        NumericDomain.Bounds above = new NumericDomain.Bounds(
                Endpoint.inclusive(Text.of("m")), null);

        Place at = standing(new ARunWithHoles(above, PlacesApart.NONE, null), ValueSet.ANY)
                .placeOf(NAME);

        assertEquals(Text.of("m"), at,
                "an end the run holds is the place taken, so the run is what the search runs"
                        + " inside");
    }

    /** Where the position stands, of a search that found somewhere for it. */
    private static NumericWitness.Standing.Found standing(SearchRegion within, ValueSet admits) {
        return assertInstanceOf(NumericWitness.Standing.Found.class,
                NumericWitness.of(within, List.of(NAME), _ -> Carrier.TEXT,
                        new WitnessSearch(_ -> new AdmittedValues.Admitted.Values(admits),
                                PatternPlan.Budget.OF_A_WITNESS::meter)),
                "the region leaves the position somewhere to stand");
    }

    /**
     * A run with places taken out of the middle of it, which refuses a row standing at one.
     *
     * <p>Both halves of what a hole is, because a test whose region only answered one of them would
     * pass on a search that asked neither: the places are what a chooser narrows by, and the refusal
     * is what a row already written at one meets.
     */
    private record ARunWithHoles(NumericDomain.Bounds bounds, PlacesApart apart, Place standing)
            implements SearchRegion {

        @Override
        public Assumption assuming(LinearForm<NumericTerm> form, Rel rel) {
            return new Assumption.Taken(this);
        }

        @Override
        public SearchRegion assuming(NumericTerm.FromOnePosition term, Place at, Rel rel) {
            return this;
        }

        @Override
        public SearchRegion apartFrom(NumericTerm.FromOnePosition term, Place at) {
            return new ARunWithHoles(bounds, PlacesApart.of(append(apart, at)), standing);
        }

        @Override
        public PlacesApart apartAt(NumericTerm.FromOnePosition term) {
            return apart;
        }

        @Override
        public SearchRegion given(Map<NumericTerm, Place> fixed) {
            return new ARunWithHoles(bounds, apart, fixed.get(NAME));
        }

        @Override
        public NumericDomain.FormProjection projectionOf(LinearForm<NumericTerm> form) {
            return new NumericDomain.FormProjection.Within(bounds);
        }

        @Override
        public Optional<EmptyInput> emptiness() {
            return standing != null && apart.has(standing)
                    ? Optional.of(new EmptyInput.ProvedByTheRules(new Emptiness.ConflictingRules()))
                    : Optional.empty();
        }

        private static List<Place> append(PlacesApart places, Place at) {
            List<Place> out = new java.util.ArrayList<>(places.places());
            out.add(at);
            return out;
        }
    }
}
