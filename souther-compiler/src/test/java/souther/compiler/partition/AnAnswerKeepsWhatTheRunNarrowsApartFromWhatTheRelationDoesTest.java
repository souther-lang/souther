package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.EmptyInput;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.PlacesApart;
import souther.compiler.numeric.Rel;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What the operators of a part narrow is of two kinds: what the run to a relation narrows, and what
 * the relation's own working narrows. A reader that holds the run against what the way states asks
 * for the first and must not be handed the second, so no way of putting answers together or
 * taking part of them loses which is which.
 */
class AnAnswerKeepsWhatTheRunNarrowsApartFromWhatTheRelationDoesTest {

    /** A region nothing here asks anything of: a constraint of one number is kept without it. */
    private static final class NeverAsked implements SearchRegion {

        @Override
        public Assumption assuming(LinearForm<NumericTerm> form, Rel rel) {
            throw new UnsupportedOperationException();
        }

        @Override
        public SearchRegion assuming(NumericTerm.FromOnePosition term, Place at, Rel rel) {
            throw new UnsupportedOperationException();
        }

        @Override
        public SearchRegion apartFrom(NumericTerm.FromOnePosition term, Place at) {
            throw new UnsupportedOperationException();
        }

        @Override
        public PlacesApart apartAt(NumericTerm.FromOnePosition term) {
            throw new UnsupportedOperationException();
        }

        @Override
        public SearchRegion given(Map<NumericTerm, Place> fixed) {
            throw new UnsupportedOperationException();
        }

        @Override
        public NumericDomain.FormProjection projectionOf(LinearForm<NumericTerm> form) {
            throw new UnsupportedOperationException();
        }

        @Override
        public Optional<EmptyInput> emptiness() {
            throw new UnsupportedOperationException();
        }
    }

    private static TakenConstraint atLeast(String place) {
        return new TakenConstraint.Affine(
                LinearForm.atom(new NumericTerm.ValueOf(TermPath.of(place))), Rel.GE);
    }

    private static DemandReading.Answered ofTheRun(TakenConstraint... narrowing) {
        return new DemandReading.Answered(List.of(narrowing), List.of(), false);
    }

    private static DemandReading.Answered ofTheRelation(TakenConstraint... narrowing) {
        return ofTheRun(narrowing).ofTheRelationItself(new NeverAsked());
    }

    @Test
    void whatARelationItselfNarrowsIsNotWhatTheRunNarrows() {
        TakenConstraint a = atLeast("a");
        DemandReading.Answered own = ofTheRelation(a);
        assertEquals(List.of(), own.onTheWay());
        assertEquals(List.of(a), own.ofTheRelation());
        assertEquals(List.of(a), own.narrowing());
    }

    @Test
    void puttingAnswersTogetherKeepsEachKindWhereItWas() {
        TakenConstraint a = atLeast("a");
        TakenConstraint b = atLeast("b");
        TakenConstraint c = atLeast("c");
        DemandReading.Answered both = ofTheRun(a).and(ofTheRelation(b)).and(ofTheRun(c));
        assertEquals(List.of(a, c), both.onTheWay());
        assertEquals(List.of(b), both.ofTheRelation());
        assertEquals(List.of(a, c, b), both.narrowing());
    }

    @Test
    void theRunIsToldBeforeTheRelationWhateverOrderTheyWereMetIn() {
        TakenConstraint a = atLeast("a");
        TakenConstraint b = atLeast("b");
        assertEquals(List.of(a, b), ofTheRelation(b).and(ofTheRun(a)).narrowing());
    }

    @Test
    void whatIsAskedOfOnlyWhatItNarrowsKeepsBothKinds() {
        TakenConstraint a = atLeast("a");
        TakenConstraint b = atLeast("b");
        DemandReading.Answered narrows = ofTheRun(a).and(ofTheRelation(b))
                .and(new DemandReading.Answered(List.of(), List.of(DemandReading.Tie.between(
                        Set.of(TermPath.of("c")))), true)).whatItNarrows();
        assertEquals(List.of(a), narrows.onTheWay());
        assertEquals(List.of(b), narrows.ofTheRelation());
        assertEquals(List.of(), narrows.tied());
        assertEquals(false, narrows.unsaid());
    }

    @Test
    void takingStatementsAwayTakesThemFromBothKinds() {
        TakenConstraint a = atLeast("a");
        TakenConstraint b = atLeast("b");
        DemandReading.Answered answered = ofTheRun(a, b).and(ofTheRelation(a, b));
        DemandReading.Answered without = answered.without(List.of((TakenConstraint.Affine) a));
        assertEquals(List.of(b), without.onTheWay());
        assertEquals(List.of(b), without.ofTheRelation());
    }

    @Test
    void applicationsBeforeAreAddedWithoutDisturbingWhatWasNarrowed() {
        TakenConstraint a = atLeast("a");
        TakenConstraint b = atLeast("b");
        DemandReading.Answered after = ofTheRun(a).and(ofTheRelation(b)).after(
                new DemandReading.PriorApplications(Optional.empty(),
                        DemandReading.Answered.NOTHING));
        assertEquals(List.of(a), after.onTheWay());
        assertEquals(List.of(b), after.ofTheRelation());
        assertEquals(1, after.before().size());
    }
}
