package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.ElementKey;
import souther.compiler.inputs.ElementProjection;
import souther.compiler.inputs.ElementValue;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.numeric.LinearForm;
import souther.compiler.types.Type;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The elements of the lists inside the elements of an outer list are chosen as one list and then
 * shared out over the lists, which keeps what they answer only where an element's answer reads
 * nothing around it: not the list holding it, nor the outer list, nor a field of the outer
 * element. Such a statement is a different one for each way of sharing the elements out
 * ({@link AStatementAtARow#answersHoweverTheElementsAreSharedOut}).
 */
class WhatAnElementAnswersIsTheSameHoweverTheElementsAreSharedOutTest {

    private static final TermPath DS = TermPath.of("ds");

    private static final TermPath FORECASTS = DS.element().then("forecasts");

    private static final TermPath AMOUNT = FORECASTS.element().then("amount");

    private static final TermPath CURRENCY = FORECASTS.element().then("currency");

    private static final TermPath FLOOR = DS.element().then("floor");

    private static final TermPath LIMIT = TermPath.of("limit");

    private static boolean sameWhereverTheyAreWritten(TermPath place) {
        Proposition holds = new Proposition.Present(new DecisionSubject.AnInput(place), true);
        return AStatementAtARow.of(holds, "f", null)
                .answersHoweverTheElementsAreSharedOut(FORECASTS, DS);
    }

    private static boolean sameWhereverTheyAreWritten(NumericTerm term) {
        return !AStatementAtARow.readsAroundTheElement(term, FORECASTS, DS);
    }

    /** What the element itself holds, and what stands outside the lists, is the same wherever the
     *  elements are written. */
    @Test
    void whatTheElementHoldsAndWhatIsOutsideTheListsIsTheSameWhereverTheyAreWritten() {
        assertTrue(sameWhereverTheyAreWritten(AMOUNT));
        assertTrue(sameWhereverTheyAreWritten(CURRENCY));
        assertTrue(sameWhereverTheyAreWritten(LIMIT));
        assertTrue(sameWhereverTheyAreWritten(new NumericTerm.ValueOf(AMOUNT)));
        assertTrue(sameWhereverTheyAreWritten(new NumericTerm.ValueOf(LIMIT)));
    }

    /** A field of the element holding the list is read of the one it is written in. */
    @Test
    void aFieldOfTheOuterElementIsNotTheSameWhereverTheElementsAreWritten() {
        assertFalse(sameWhereverTheyAreWritten(FLOOR));
        assertFalse(sameWhereverTheyAreWritten(new NumericTerm.ValueOf(FLOOR)));
    }

    /** What is read of one whole list, or of the outer list, depends on which elements are in it. */
    @Test
    void whatIsReadOfAWholeListIsNotTheSameWhereverTheElementsAreWritten() {
        assertFalse(sameWhereverTheyAreWritten(FORECASTS));
        assertFalse(sameWhereverTheyAreWritten(DS));
        assertFalse(sameWhereverTheyAreWritten(NumericTerm.Multiplicity.of(FORECASTS, CURRENCY)));
    }

    /** What the elements of every list come to under a value is the elements', wherever they are
     *  written. */
    @Test
    void whatTheElementsOfEveryListComeToIsTheSameWhereverTheyAreWritten() {
        NumericTerm total = NumericTerm.GatheredUnderItsKey.of(FORECASTS.element(),
                new ElementKey.At(ElementProjection.ofFields(List.of("currency"))),
                new ElementValue.Affine(LinearForm.atom(
                        ElementProjection.ofFields(List.of("amount")))),
                Type.Prim.INT, NumericTerm.GatheredUnderItsKey.Gathering.TOTAL, null);
        assertTrue(sameWhereverTheyAreWritten(total));
    }

    /** How often a value occurs among the elements of every list is the elements', wherever they
     *  are written. */
    @Test
    void howOftenAValueOccursAmongTheElementsOfEveryListIsTheSameWhereverTheyAreWritten() {
        assertTrue(sameWhereverTheyAreWritten(NumericTerm.OccurrencesOfItsValue.of(
                new RunSource.FlattenedOccurrences(CURRENCY), null)));
    }
}
