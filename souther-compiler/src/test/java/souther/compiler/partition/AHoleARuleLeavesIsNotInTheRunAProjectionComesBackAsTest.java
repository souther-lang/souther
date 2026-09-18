package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.EmptyInput;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;

import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a rule holds a position away from is put back into the question, and a condition over a form
 * is carried rather than read as a run.
 *
 * <p>A region holds every cut the way took in and answers about a term as a pair of ends. Those are
 * not the same thing: a rule holding a term away from one value inside a run leaves a set with a
 * hole in it, and the tightest pair of ends around that set is the run entire. So the ends are what
 * the region has to say, and the rest is asked of the cuts — which is the difference between a
 * search that may say the rules leave nothing and one that tried the one number a rule took out.
 */
class AHoleARuleLeavesIsNotInTheRunAProjectionComesBackAsTest {

    private static final Carrier COUNTS = new Carrier.Whole();

    private static final NumericTerm.FromOnePosition LENGTH =
            new NumericTerm.ValueOf(TermPath.of("b"));

    private static final NumericTerm.FromOnePosition BESIDE =
            new NumericTerm.ValueOf(TermPath.of("c"));

    /** The anchor a report would name the condition by, which nothing here asks about. */
    private static final ConditionReportAnchor WHERE =
            new ConditionReportAnchor.WhereTheReadingMetIt("m", new ConditionOccurrence("b", 0));

    /** A region that says the same thing about every term, so what the cuts add is what is read. */
    private record Leaving(NumericDomain.Bounds bounds) implements SearchRegion {

        @Override
        public Assumption assuming(LinearForm<NumericTerm> form, Rel rel) {
            return new Assumption.Taken(this);
        }

        @Override
        public SearchRegion assuming(NumericTerm.FromOnePosition term, Place at, Rel rel) {
            return this;
        }

        @Override
        public SearchRegion given(Map<NumericTerm, Place> fixed) {
            return this;
        }

        @Override
        public SearchRegion apartFrom(NumericTerm.FromOnePosition term, Place at) {
            return this;
        }

        @Override
        public NumericDomain.FormProjection projectionOf(LinearForm<NumericTerm> form) {
            return new NumericDomain.FormProjection.Within(bounds);
        }

        @Override
        public Optional<EmptyInput> emptiness() {
            return Optional.empty();
        }
    }

    /** A region the rules leave the term nowhere in. */
    private record LeavingNothing() implements SearchRegion {

        @Override
        public Assumption assuming(LinearForm<NumericTerm> form, Rel rel) {
            return new Assumption.Taken(this);
        }

        @Override
        public SearchRegion assuming(NumericTerm.FromOnePosition term, Place at, Rel rel) {
            return this;
        }

        @Override
        public SearchRegion given(Map<NumericTerm, Place> fixed) {
            return this;
        }

        @Override
        public SearchRegion apartFrom(NumericTerm.FromOnePosition term, Place at) {
            return this;
        }

        @Override
        public NumericDomain.FormProjection projectionOf(LinearForm<NumericTerm> form) {
            return new NumericDomain.FormProjection.NothingIsLeft();
        }

        @Override
        public Optional<EmptyInput> emptiness() {
            return Optional.empty();
        }
    }

    private static Level at(long value) {
        return new Level.OnACarrier(COUNTS, Count.of(value));
    }

    private static OnTheWay.TakenIn awayFrom(NumericTerm.FromOnePosition term, long value) {
        return new OnTheWay.TakenIn(WHERE, new TakenConstraint.AwayFrom(term, Count.of(value)));
    }

    private static OnTheWay.TakenIn overAForm(NumericTerm.FromOnePosition one,
                                              NumericTerm.FromOnePosition other) {
        return new OnTheWay.TakenIn(WHERE, new TakenConstraint.Affine(
                LinearForm.<NumericTerm>atom(one).plus(LinearForm.<NumericTerm>atom(other)),
                Rel.GE));
    }

    private static NumbersAskedFor asked(NumericDomain.Bounds leaves, OnTheWay.TakenIn... cuts) {
        return NumbersAskedFor.askedOf(LENGTH, new Leaving(leaves), COUNTS, List.of(cuts));
    }

    /**
     * The value a rule holds the position away from is out of the question.
     *
     * <p>Asserted against the region's own answer, so that the hole is shown to come from the cut:
     * the ends it hands over hold the value, and the question does not.
     */
    @Test
    void aValueARuleHoldsThePositionAwayFromIsNotAsked() {
        NumbersAskedFor asked = asked(NumericDomain.Bounds.OPEN, awayFrom(LENGTH, 1));

        assertTrue(asked.values().contains(at(0)), "what lies under the hole is asked for");
        assertTrue(asked.values().contains(at(2)), "and what lies over it");
        assertFalse(asked.values().contains(at(1)), "and the value the rule takes out is not");
    }

    /** The ends the region hands over are the question's, and a hole inside them stays a hole. */
    @Test
    void theHoleIsTakenOutOfTheRunTheRegionLeaves() {
        NumbersAskedFor asked = asked(
                new NumericDomain.Bounds(Endpoint.inclusive(Count.of(0)),
                        Endpoint.inclusive(Count.of(4))),
                awayFrom(LENGTH, 1));

        assertTrue(asked.values().contains(at(0)), "the region's lower end is asked for");
        assertTrue(asked.values().contains(at(4)), "and its upper end");
        assertFalse(asked.values().contains(at(1)), "with the value the rule takes out left out");
        assertFalse(asked.values().contains(at(5)), "and nothing past what the region leaves");
    }

    /** An end the region does not reach is not asked for, which is what an exclusive end means. */
    @Test
    void anEndTheRegionDoesNotReachIsNotAskedFor() {
        NumbersAskedFor asked = asked(new NumericDomain.Bounds(
                new Endpoint(Count.of(0), false), new Endpoint(Count.of(4), false)));

        assertFalse(asked.values().contains(at(0)), "an end the region holds open is outside");
        assertTrue(asked.values().contains(at(1)), "and what lies inside it is asked for");
        assertFalse(asked.values().contains(at(4)), "on either side");
    }

    /** A rule about another position takes nothing out of this one's question. */
    @Test
    void aRuleAboutAnotherPositionIsNotAskedOfThisOne() {
        NumbersAskedFor asked = asked(NumericDomain.Bounds.OPEN, awayFrom(BESIDE, 1));

        assertTrue(asked.values().contains(at(1)),
                "a hole in another position's order is not a hole in this one's");
        assertTrue(asked.isWalkedWhole(), "and nothing about it is in the way of walking this one");
    }

    /**
     * A condition over a form of two positions is carried, and leaves this one every number.
     *
     * <p>Both halves. Which numbers it leaves here is whatever the other position took, so nothing
     * is taken out — and a walk of what is left is not a walk of the question.
     */
    @Test
    void aConditionOverAFormLeavesTheTermEveryNumberAndIsCarried() {
        OnTheWay.TakenIn form = overAForm(LENGTH, BESIDE);
        NumbersAskedFor asked = asked(NumericDomain.Bounds.OPEN, form);

        assertTrue(asked.values().contains(at(7)), "nothing of the order is taken away");
        assertEquals(List.of(form.taken()), asked.onlyTogether(),
                "and the condition is what says why that is not the whole answer");
        assertFalse(asked.isWalkedWhole(), "so the term is not walked whole by walking its order");
    }

    /** A form of one term is the region's to answer, and adds nothing here. */
    @Test
    void aFormOfOneTermIsAlreadyWhatTheRegionLeaves() {
        OnTheWay.TakenIn ofOne = new OnTheWay.TakenIn(WHERE, new TakenConstraint.Affine(
                LinearForm.<NumericTerm>atom(LENGTH), Rel.GE));
        NumbersAskedFor asked = asked(
                new NumericDomain.Bounds(Endpoint.inclusive(Count.of(2)), null), ofOne);

        assertTrue(asked.isWalkedWhole(),
                "a rule about the term itself leaves it a set of its own");
        assertFalse(asked.values().contains(at(1)),
                "and what it leaves is the run the region came back with");
        assertTrue(asked.values().contains(at(2)), "from its end up");
    }

    /** Both kinds at once keep both: the hole is taken out and the form is still carried. */
    @Test
    void aHoleAndAConditionOverAFormAreBothKept() {
        OnTheWay.TakenIn form = overAForm(LENGTH, BESIDE);
        NumbersAskedFor asked = asked(NumericDomain.Bounds.OPEN, awayFrom(LENGTH, 1), form);

        assertFalse(asked.values().contains(at(1)), "the hole is out of the question");
        assertTrue(asked.values().contains(at(2)), "and the rest of the order is in it");
        assertEquals(List.of(form.taken()), asked.onlyTogether(),
                "with the condition over the form carried beside it");
    }

    /** A region that leaves the term nowhere is the whole of what is asked of it. */
    @Test
    void aTermTheRulesLeaveNowhereIsAskedForNothing() {
        NumbersAskedFor asked =
                NumbersAskedFor.askedOf(LENGTH, new LeavingNothing(), COUNTS, List.of());

        assertEquals(List.of(), asked.values().parts(), "nothing is left to ask about");
        assertTrue(asked.isWalkedWhole(), "and that is the whole of the answer");
    }
}
