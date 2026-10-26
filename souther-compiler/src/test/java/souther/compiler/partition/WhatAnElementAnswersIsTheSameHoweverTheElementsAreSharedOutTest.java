package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import net.unit8.notation199x.pattern.PatternMeaning;
import souther.compiler.meaning.StringsLanguage;

import souther.compiler.inputs.Case;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.ElementKey;
import souther.compiler.inputs.ElementProjection;
import souther.compiler.inputs.ElementValue;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.PositionsAStatementReads;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.WaysSamples;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The elements of the lists inside the elements of an outer list are chosen as one list and then
 * shared out over the lists, which keeps what they answer only where an element's answer reads
 * nothing around it: not the list holding it, nor the outer list, nor a field of the outer
 * element, nor which of the elements holding a value comes last. Such a statement is a different
 * one for each way of sharing the elements out
 * ({@link AStatementAtARow#answersHoweverTheElementsAreSharedOut}).
 *
 * <p>That is asked of the statement itself, so every kind of statement is decided here, and a kind
 * added to {@link Proposition} is a test that fails until it is.
 */
class WhatAnElementAnswersIsTheSameHoweverTheElementsAreSharedOutTest {

    private static final TermPath DS = TermPath.of("ds");

    private static final TermPath FORECASTS = DS.element().then("forecasts");

    private static final TermPath AMOUNT = FORECASTS.element().then("amount");

    private static final TermPath CURRENCY = FORECASTS.element().then("currency");

    private static final TermPath FLOOR = DS.element().then("floor");

    private static final TermPath LIMIT = TermPath.of("limit");

    private static DecisionSubject at(TermPath place) {
        return new DecisionSubject.AnInput(place);
    }

    private static Proposition above(NumericTerm term) {
        return new Proposition.Compared(new Relation.Affine(new LinearForm<>(ExactRatio.ZERO,
                Map.of(new DecisionAtom.OfTheInput(term), ExactRatio.ONE)), Rel.GT), true);
    }

    private static boolean sameWhereverTheyAreWritten(Proposition stated) {
        return AStatementAtARow.of(stated, "f", null)
                .answersHoweverTheElementsAreSharedOut(FORECASTS, DS);
    }

    private static boolean sameWhereverTheyAreWritten(NumericTerm term) {
        return !AStatementAtARow.readsAroundTheElement(term, FORECASTS, DS);
    }

    /**
     * Every kind of statement there is, with what it says of the element itself and what it says
     * of something around it. The kinds that are put to no row because nothing reads them are
     * not constructed here, and are not the same wherever the elements are written either: they
     * are no place of the input.
     */
    @Test
    void everyKindOfStatementIsDecidedHere() {
        CasesLeft cases = CasesLeft.ofEach(List.of(Refinement.of(
                new Case.SumCase(TypeSymbols.declared(new TypeKey("probe", "Open")), true))));
        Map<Class<?>, Boolean[]> decided = new LinkedHashMap<>();
        // The element itself, then something around it; null where the kind reads no place.
        decided.put(Proposition.Always.class, new Boolean[] {
            sameWhereverTheyAreWritten(new Proposition.Always(true)), null});
        decided.put(Proposition.Compared.class, new Boolean[] {
            !readsAround(above(new NumericTerm.ValueOf(AMOUNT))),
            !readsAround(above(new NumericTerm.ValueOf(FLOOR)))});
        decided.put(Proposition.Truth.class, new Boolean[] {
            sameWhereverTheyAreWritten(new Proposition.Truth(at(AMOUNT), true)),
            sameWhereverTheyAreWritten(new Proposition.Truth(at(FLOOR), true))});
        decided.put(Proposition.Present.class, new Boolean[] {
            sameWhereverTheyAreWritten(new Proposition.Present(at(CURRENCY), true)),
            sameWhereverTheyAreWritten(new Proposition.Present(at(FORECASTS), true))});
        decided.put(Proposition.InTheStrings.class, new Boolean[] {
            sameWhereverTheyAreWritten(new Proposition.InTheStrings(
                    new Proposition.InTheStrings.Strings.AtAPosition(AMOUNT),
                    new StringsLanguage(PatternMeaning.text("ab")), true)),
            sameWhereverTheyAreWritten(new Proposition.InTheStrings(
                    new Proposition.InTheStrings.Strings.AtAPosition(FLOOR),
                    new StringsLanguage(PatternMeaning.text("ab")), true))});
        decided.put(Proposition.InCases.class, new Boolean[] {
            sameWhereverTheyAreWritten(new Proposition.InCases(at(CURRENCY), cases, true)),
            sameWhereverTheyAreWritten(new Proposition.InCases(at(FLOOR), cases, true))});
        decided.put(Proposition.SameValue.class, new Boolean[] {
            sameWhereverTheyAreWritten(new Proposition.SameValue(at(CURRENCY), at(AMOUNT), true)),
            sameWhereverTheyAreWritten(new Proposition.SameValue(at(CURRENCY), at(FLOOR), true))});
        decided.put(Proposition.LastToHold.class, new Boolean[] {
            null,
            sameWhereverTheyAreWritten(new Proposition.LastToHold(at(FORECASTS), at(CURRENCY),
                    true))});
        Proposition inside = new Proposition.Present(at(CURRENCY), true);
        Proposition around = new Proposition.Present(at(FLOOR), true);
        decided.put(Proposition.All.class, new Boolean[] {
            sameWhereverTheyAreWritten(new Proposition.All(List.of(inside, inside))),
            sameWhereverTheyAreWritten(new Proposition.All(List.of(inside, around)))});
        decided.put(Proposition.Any.class, new Boolean[] {
            sameWhereverTheyAreWritten(new Proposition.Any(List.of(inside, inside))),
            sameWhereverTheyAreWritten(new Proposition.Any(List.of(inside, around)))});
        decided.put(Proposition.WhereItAnswers.class, new Boolean[] {
            sameWhereverTheyAreWritten(new Proposition.WhereItAnswers(inside, inside)),
            sameWhereverTheyAreWritten(new Proposition.WhereItAnswers(inside, around))});
        decided.put(Proposition.OnAnApplication.class, new Boolean[] {
            sameWhereverTheyAreWritten(new Proposition.OnAnApplication(List.of(inside,
                    new Proposition.Truth(at(AMOUNT), true)))),
            sameWhereverTheyAreWritten(new Proposition.OnAnApplication(List.of(inside,
                    around)))});
        decided.put(Proposition.SoManyHold.class, new Boolean[] {
            sameWhereverTheyAreWritten(Proposition.SoManyHold.counting(List.of(inside), List.of(1),
                    List.of(1))),
            sameWhereverTheyAreWritten(Proposition.SoManyHold.counting(List.of(around), List.of(1),
                    List.of(1)))});
        decided.put(Proposition.OfTheWays.class, new Boolean[] {
            sameWhereverTheyAreWritten(WaysSamples.over(inside)),
            sameWhereverTheyAreWritten(WaysSamples.over(around))});
        // A quantifier over a list reads the list.
        decided.put(Proposition.Some.class, new Boolean[] {
            null, sameWhereverTheyAreWritten(new Proposition.Some(at(FORECASTS), inside, true))});

        decided.forEach((kind, answers) -> {
            if (answers[0] != null) {
                assertTrue(answers[0], kind.getSimpleName() + " of the element itself");
            }
            if (answers[1] != null) {
                assertFalse(answers[1], kind.getSimpleName() + " of something around it");
            }
        });
        Set<Class<?>> unread = Set.of(Proposition.Unread.class, Proposition.Carried.class,
                Proposition.SomeReachable.class);
        Set<Class<?>> every = Arrays.stream(Proposition.class.getPermittedSubclasses())
                .collect(Collectors.toSet());
        Set<Class<?>> accounted = new HashSet<>(decided.keySet());
        accounted.addAll(unread);
        assertEquals(every, accounted, "a kind of statement nobody decided whether it is the same"
                + " wherever the elements are written");
    }

    /** For a comparison, which a row is put to only with the numbers of an input read: the places
     *  it is read off are asked of the statement all the same. */
    private static boolean readsAround(Proposition stated) {
        return PositionsAStatementReads.everyPlaceOf(stated)
                .map(places -> places.stream().anyMatch(place -> place.isAtOrUnder(DS)
                        && !place.isAtOrUnder(FORECASTS.element())))
                .orElse(true);
    }

    /** What the element itself holds, and what stands outside the lists, is the same wherever the
     *  elements are written. */
    @Test
    void whatTheElementHoldsAndWhatIsOutsideTheListsIsTheSameWhereverTheyAreWritten() {
        assertTrue(sameWhereverTheyAreWritten(new NumericTerm.ValueOf(AMOUNT)));
        assertTrue(sameWhereverTheyAreWritten(new NumericTerm.ValueOf(LIMIT)));
        assertTrue(sameWhereverTheyAreWritten(new Proposition.Present(at(LIMIT), true)));
    }

    /** A field of the element holding the list is read of the one it is written in. */
    @Test
    void aFieldOfTheOuterElementIsNotTheSameWhereverTheElementsAreWritten() {
        assertFalse(sameWhereverTheyAreWritten(new NumericTerm.ValueOf(FLOOR)));
    }

    /** What is read of one whole list, or of the outer list, depends on which elements are in it. */
    @Test
    void whatIsReadOfAWholeListIsNotTheSameWhereverTheElementsAreWritten() {
        assertFalse(sameWhereverTheyAreWritten(new Proposition.Present(at(DS), true)));
        assertFalse(sameWhereverTheyAreWritten(
                NumericTerm.Multiplicity.of(FORECASTS, CURRENCY)));
    }

    /** Which element comes last among those holding a value is told in the list that holds them:
     *  two forecasts of one currency are one last in a list and two in two. */
    @Test
    void whichElementIsTheLastOfThoseHoldingAValueIsNotTheSameWhereverTheyAreWritten() {
        assertFalse(sameWhereverTheyAreWritten(new Proposition.LastToHold(at(FORECASTS),
                at(CURRENCY), true)));
        assertFalse(sameWhereverTheyAreWritten(new Proposition.All(List.of(
                new Proposition.Present(at(AMOUNT), true),
                new Proposition.LastToHold(at(FORECASTS), at(CURRENCY), true)))));
        Proposition last = new Proposition.LastToHold(at(FORECASTS), at(CURRENCY), true);
        assertEquals(AStatementAtARow.TurnsOn.OTHER_ELEMENTS,
                AStatementAtARow.of(last, "f", null).turnsOnAmong(FORECASTS, null,
                        Optional.of(DS)));
        assertTrue(AStatementAtARow.of(last, "f", null).readsTheValueAt(FORECASTS,
                new Quantity.TheValue.AtAPlace(at(CURRENCY)), Optional.of(DS)));
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
        assertTrue(sameWhereverTheyAreWritten(NumericTerm.OccurrencesOfItsValue.of(
                new RunSource.FlattenedOccurrences(CURRENCY), null)));
    }
}
