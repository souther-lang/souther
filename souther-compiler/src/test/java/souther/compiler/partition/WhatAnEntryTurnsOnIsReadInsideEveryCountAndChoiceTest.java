package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.PositionsAStatementReads.ReadSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What an entry on a way turns on ({@link WayToTheBorder#turnsOn}) is read inside every statement
 * it counts, held and failing, and every alternative it leaves a row: a condition with no words,
 * or a statement only a run checks reading a value a binding holds, anywhere inside it leaves what
 * it turns on not known, and it is never shown to ask nothing of a place
 * ({@link WayToTheBorder#asksNothingOf}).
 */
class WhatAnEntryTurnsOnIsReadInsideEveryCountAndChoiceTest {

    private static final ConditionOccurrence CONDITION =
            new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, 0);
    private static final ConditionReportAnchor WHERE =
            new ConditionReportAnchor.WhereTheReadingMetIt("m", CONDITION);
    private static final TermPath A = TermPath.of("r").then("a");
    private static final TermPath B = TermPath.of("r").then("b");

    @Test
    void aCountOfTruthsTurnsOnTheirPlaces() {
        OnTheWay counted = countOf(truth(A, true), truth(A, false));
        assertEquals(Set.of(new ReadSubject.At(A)), WayToTheBorder.turnsOn(counted));
        assertTrue(WayToTheBorder.asksNothingOf(B, counted));
        assertFalse(WayToTheBorder.asksNothingOf(A, counted));
    }

    @Test
    void aCountWithAConditionOfNoWordsInsideTurnsOnWhatIsNotKnown() {
        assertNotKnown(countOf(truth(A, true), declined()));
        assertNotKnown(countOf(truth(A, true), truth(A, false), declined()));
    }

    @Test
    void aCountWithAChoiceInsideTurnsOnWhatEveryWayOfItDoes() {
        OnTheWay choice = OnTheWay.OneOf.of(CONDITION, WHERE,
                List.of(List.of(truth(A, true)), List.of(declined())), Optional.empty());
        assertNotKnown(countOf(truth(A, true), choice));
    }

    @Test
    void aCountOfAStatementOnlyARunChecksTurnsOnTheValueItReads() {
        OnTheWay counted = countOf(truth(A, true), forTheRun());
        Set<ReadSubject> on = WayToTheBorder.turnsOn(counted);
        assertTrue(on == null || on.stream().anyMatch(ReadSubject.Bound.class::isInstance),
                () -> "a value a binding holds is about every place: " + on);
        assertFalse(WayToTheBorder.asksNothingOf(B, counted));
    }

    private static void assertNotKnown(OnTheWay entry) {
        assertEquals(null, WayToTheBorder.turnsOn(entry), entry::toString);
        assertEquals(null, WayToTheBorder.placesTurnedOn(List.of(entry)));
        assertFalse(WayToTheBorder.asksNothingOf(B, entry));
    }

    /** A count of one statement, {@code holding} where it holds and {@code failing} where not. */
    private static OnTheWay countOf(OnTheWay holding, OnTheWay... failing) {
        Proposition stated = new Proposition.Truth(new DecisionSubject.AnInput(A), true);
        return new OnTheWay.Counted(CONDITION, WHERE,
                List.of(new OnTheWay.Counted.Statement(1, List.of(holding), List.of(failing))),
                List.of(1), Proposition.SoManyHold.counting(List.of(stated), List.of(1),
                        List.of(1)));
    }

    private static OnTheWay truth(TermPath at, boolean holds) {
        return new OnTheWay.TakenIn(WHERE, new RowDemand.ATruth(at, holds));
    }

    private static OnTheWay declined() {
        return new OnTheWay.Declined(CONDITION, WHERE,
                new WhyNotTaken.OutsideDomain(WhyNotTaken.DomainLimit.A_QUANTITY_ON_NO_ORDER));
    }

    /** {@code n >= 1}, of the element {@code n} of {@code List.rangeInclusive(0, r.days)}. */
    private static OnTheWay forTheRun() {
        Quantity.OfABinding n = new Quantity.OfABinding(
                new BindingId(new BindingOwner.OfValue("m", "f"), 0), List.of(), Type.INT,
                Optional.empty(), Optional.of(new Quantity.AWholeNumberInTurn(
                        LinearForm.constant(ExactRatio.ZERO),
                        new LinearForm<>(ExactRatio.ZERO, Map.of(new NumericTerm.ValueOf(
                                TermPath.of("r").then("days")), ExactRatio.ONE)))));
        Proposition stated = new Proposition.Compared(new Relation.Affine(
                new LinearForm<>(ExactRatio.of(-1), Map.of(n, ExactRatio.ONE)), Rel.GE), true);
        return new OnTheWay.TakenIn(WHERE, new RowDemand.ForTheRun(stated,
                RowDemand.NoComposer.A_REMAINDER_OF_A_FORM, List.of(), Optional.empty()));
    }
}
