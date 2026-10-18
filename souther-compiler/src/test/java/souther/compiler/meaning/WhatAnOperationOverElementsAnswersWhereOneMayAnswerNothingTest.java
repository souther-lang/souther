package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.semantics.HowAClosureIsApplied;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What an operation over elements answers where what it states of one element answers nothing on
 * some rows: what the operation answers turns on which element a run reaches first.
 *
 * <p>Each element here states {@code s} where {@code d} holds and nothing elsewhere, as a quotient
 * by what the element holds does where its divisor is nought. A row is a choice of {@code d} and
 * {@code s} for each element, and what a statement comes to on it is held, failed, or neither —
 * the run stopped.
 */
class WhatAnOperationOverElementsAnswersWhereOneMayAnswerNothingTest {

    private static final TermPath XS = TermPath.of("xs");
    private static final DecisionSubject CONTAINER = new DecisionSubject.AnInput(XS);
    private static final TermPath DIVIDES = XS.element().then("d");
    private static final TermPath STATES = XS.element().then("s");

    /** What one row comes to of a statement: held, failed, or no way at all. */
    private enum Outcome { HOLDS, FAILS, NO_WAY }

    private static Proposition truth(TermPath at) {
        return new Proposition.Truth(new DecisionSubject.AnInput(at), true);
    }

    private static Derivation truthAt(TermPath at) {
        return new Derivation.ATruthOfASubject(new DecisionSubject.AnInput(at), true);
    }

    /** What the element written as {@code name} states, where its own divisor answers. */
    private static Derivation writtenOut(String name) {
        return new Derivation.WhereItAnswers(truthAt(TermPath.of(name + "d")),
                truthAt(TermPath.of(name + "s")));
    }

    /**
     * What {@code stated} comes to on the row each written element is given on: {@code -1} for an
     * element whose divisor is nought, and otherwise whether it states its truth.
     */
    private static Outcome on(Proposition stated, String names, int... row) {
        List<Proposition> given = new ArrayList<>();
        for (int at = 0; at < row.length; at++) {
            String name = String.valueOf(names.charAt(at));
            Proposition divides = truth(TermPath.of(name + "d"));
            given.add(row[at] < 0 ? divides.denied() : divides);
            if (row[at] >= 0) {
                Proposition states = truth(TermPath.of(name + "s"));
                given.add(row[at] == 1 ? states : states.denied());
            }
        }
        Proposition onTheRow = Proposition.all(given);
        if (TruthTable.holdsWhateverItsPartsAre(
                Proposition.any(List.of(onTheRow.denied(), stated)))) {
            return Outcome.HOLDS;
        }
        if (TruthTable.holdsWhateverItsPartsAre(
                Proposition.any(List.of(onTheRow.denied(), stated.denied())))) {
            return Outcome.FAILS;
        }
        return Outcome.NO_WAY;
    }

    private static Proposition concluded(Derivation derivation) {
        return derivation.concludes(Optional.empty());
    }

    /**
     * An operation stopping at the first element holding it goes through values written out in the
     * order they were written: the same two values, the other way round, come to something else.
     * Read side by side, {@code [0, 1]} would hold for its second element, which no run reaches.
     */
    @Test
    void valuesWrittenOutAreAskedInTheOrderTheyWereWritten() {
        Proposition any = concluded(new Derivation.OverElementsWrittenOut(
                List.of(writtenOut("a"), writtenOut("b")), true,
                HowTheElementsAreAsked.UNTIL_ONE_MEETS_IT));
        assertEquals(Outcome.NO_WAY, on(any, "ab", -1, 1));
        assertEquals(Outcome.HOLDS, on(any, "ab", 1, -1));
        assertEquals(Outcome.NO_WAY, on(any, "ab", 0, -1));
        assertEquals(Outcome.FAILS, on(any, "ab", 0, 0));
        assertEquals(Outcome.HOLDS, on(any, "ab", 0, 1));
    }

    /**
     * Stopping at the first element that fails, as {@code List.all} does: some element failing,
     * in turn, and what the operation answers is its denial. A failing first value answers before
     * the second is asked; a first that stops the run answers nothing however the second comes out.
     */
    @Test
    void stoppingAtTheFirstThatFailsIsTheSameOrderDenied() {
        Proposition all = concluded(new Derivation.OverElementsWrittenOut(
                List.of(writtenOut("a"), writtenOut("b")), false,
                HowTheElementsAreAsked.UNTIL_ONE_MEETS_IT)).denied();
        assertEquals(Outcome.FAILS, on(all, "ab", 0, -1));
        assertEquals(Outcome.NO_WAY, on(all, "ab", -1, 0));
        assertEquals(Outcome.NO_WAY, on(all, "ab", 1, -1));
        assertEquals(Outcome.HOLDS, on(all, "ab", 1, 1));
    }

    /** Asking every value, an operation answers only where every one of them did. */
    @Test
    void askingEveryValueAnswersOnlyWhereEachDid() {
        Proposition counted = concluded(new Derivation.OverElementsWrittenOut(
                List.of(writtenOut("a"), writtenOut("b")), true, HowTheElementsAreAsked.EVERY_ONE));
        assertEquals(Outcome.NO_WAY, on(counted, "ab", 1, -1));
        assertEquals(Outcome.NO_WAY, on(counted, "ab", -1, 1));
        assertEquals(Outcome.HOLDS, on(counted, "ab", 0, 1));
        assertEquals(Outcome.FAILS, on(counted, "ab", 0, 0));
    }

    /** Where nothing says how they are gone through, it is not read. */
    @Test
    void valuesGoneThroughNoSaidWayAreNotRead() {
        Proposition stated = concluded(new Derivation.OverElementsWrittenOut(
                List.of(writtenOut("a"), writtenOut("b")), true, HowTheElementsAreAsked.NOT_SAID));
        assertEquals(new Proposition.Unread(Optional.empty(), 0,
                new WhyUnread.WhichElementARunStopsAt(), false, true), stated);
    }

    /**
     * Some element of a container meeting a statement that answers nothing on some elements: some
     * element where it answers and holds ({@code T}), and every element answering ({@code G}), each
     * of them a quantifier over a statement every row answers. Asking every element, the operation
     * answers where {@code G} holds; asking each in turn in an order the rows choose, where some
     * element meets it or {@code G} holds. Its denial is then every element answering and none
     * meeting it, which a run that stopped at an element never comes to.
     */
    @Test
    void someElementIsReadOfWhereItHoldsAndWhereEveryElementAnswers() {
        Derivation element = new Derivation.WhereItAnswers(truthAt(DIVIDES), truthAt(STATES));
        Proposition some = new Proposition.Some(CONTAINER,
                Proposition.all(List.of(truth(DIVIDES), truth(STATES))), true);
        Proposition every = new Proposition.Some(CONTAINER, truth(DIVIDES).denied(), false);
        assertEquals(Proposition.whereItAnswers(every, some),
                concluded(new Derivation.SomeElementMeeting(CONTAINER, element, true,
                        Optional.empty(), HowTheElementsAreAsked.EVERY_ONE)));
        Proposition inTheRowsOrder = concluded(new Derivation.SomeElementMeeting(CONTAINER,
                element, true, Optional.empty(),
                HowTheElementsAreAsked.UNTIL_ONE_MEETS_IT_IN_AN_ORDER_OF_THE_ROWS));
        assertEquals(Proposition.whereItAnswers(Proposition.any(List.of(some, every)), some),
                inTheRowsOrder);
        assertEquals(Proposition.whereItAnswers(Proposition.any(List.of(some, every)),
                some.denied()), inTheRowsOrder.denied());
    }

    /**
     * In an order the rows do not choose, which element comes first is the order's, and nothing
     * says it: not read. Unless whether an element answers is the same for every element — a
     * divisor the same on every application — when the run stops at the first it reaches where it
     * stops at any, and the operation answers where every element does.
     */
    @Test
    void inAnOrderTheRowsDoNotChooseOnlyADivisorTheSameForEveryElementIsRead() {
        Derivation element = new Derivation.WhereItAnswers(truthAt(DIVIDES), truthAt(STATES));
        assertEquals(new Proposition.Unread(Optional.empty(), 0,
                        new WhyUnread.WhichElementARunStopsAt(), false, true),
                concluded(new Derivation.SomeElementMeeting(CONTAINER, element, true,
                        Optional.empty(), HowTheElementsAreAsked.UNTIL_ONE_MEETS_IT)));
        TermPath divisor = TermPath.of("d");
        Derivation size = new Derivation.WrittenOut(true);
        Derivation alike = new Derivation.WhereItAnswers(truthAt(divisor), truthAt(STATES));
        Proposition some = new Proposition.Some(CONTAINER, truth(STATES), true);
        Proposition every = Proposition.all(List.of(truth(divisor).denied(),
                concluded(size))).denied();
        assertEquals(Proposition.whereItAnswers(every,
                        Proposition.all(List.of(truth(divisor), some))),
                concluded(new Derivation.SomeElementMeeting(CONTAINER, alike, true,
                        Optional.of(size), HowTheElementsAreAsked.UNTIL_ONE_MEETS_IT)));
    }

    /**
     * Where a statement answers is said with nothing in it that answers nothing, wherever in the
     * statement the part that may stands: behind a part worked out before it, the statement
     * answers where that part fails, or holds and the divisor is not nought.
     */
    @Test
    void whereAStatementAnswersIsSaidOnEveryRow() {
        Proposition before = truth(TermPath.of("c"));
        Proposition stated = Proposition.all(List.of(before,
                Proposition.whereItAnswers(truth(DIVIDES), truth(STATES))));
        Proposition answers = Proposition.whereItAnswersAtAll(stated);
        assertEquals(false, Proposition.mayAnswerNothing(answers));
        assertEquals(Proposition.any(List.of(
                        Proposition.all(List.of(before, truth(DIVIDES), truth(STATES))),
                        Proposition.whereItHolds(stated.denied()))),
                answers);
        assertEquals(false, Proposition.mayAnswerNothing(Proposition.whereItAnswersAtAll(
                Proposition.whereItAnswers(Proposition.any(List.of(stated, stated.denied())),
                        truth(TermPath.of("e"))))));
    }

    /**
     * An arm about the entry a lookup picked out works out that one entry and no other, so it
     * answers where that entry does: some element picked out and meeting the statement where it
     * holds, read on the rows no element picked out answers nothing on.
     */
    @Test
    void anArmAboutTheEntryPickedOutAnswersWhereThatEntryDoes() {
        TermPath key = XS.element().then("k");
        Derivation picked = new Derivation.SomeElementMeeting(CONTAINER, truthAt(key), true,
                Optional.empty(), HowTheElementsAreAsked.NOT_SAID);
        Derivation states = new Derivation.WhereItAnswers(truthAt(DIVIDES), truthAt(STATES));
        Proposition stated = concluded(new Derivation.MatchArms(List.of(
                new Derivation.MatchArms.Arm(picked, states, true),
                new Derivation.MatchArms.Arm(new Derivation.UnderADenial(picked, true),
                        new Derivation.WrittenOut(false)))));
        Proposition entry = Proposition.all(List.of(truth(key),
                Proposition.whereItAnswers(truth(DIVIDES), truth(STATES))));
        Proposition meets = Proposition.whereItAnswers(
                new Proposition.Some(CONTAINER,
                        Proposition.whereItAnswersAtAll(entry).denied(), false),
                new Proposition.Some(CONTAINER, Proposition.whereItHolds(entry), true));
        assertEquals(meets, stated);
    }

    /**
     * A quantifier, a count or a search is of statements answering on every row: what each of
     * them comes to where one of its statements answers nothing is said where it is read, and
     * a reading that did not say it is stopped here.
     */
    @Test
    void aQuantifierOrACountOverAStatementThatMayAnswerNothingIsRefused() {
        Proposition stops = Proposition.whereItAnswers(truth(DIVIDES), truth(STATES));
        assertThrows(IllegalArgumentException.class,
                () -> new Proposition.Some(CONTAINER, stops, true));
        assertThrows(IllegalArgumentException.class,
                () -> new Quantity.HowManyMeet(CONTAINER, stops));
        assertThrows(IllegalArgumentException.class,
                () -> new Quantity.HowManyHold(List.of(stops)));
        assertThrows(IllegalArgumentException.class,
                () -> new Proposition.SomeReachable(XS, XS, List.of("below"), stops,
                        Optional.empty(), true));
    }

    /**
     * Applied to every value, an application is made only where each one before it answered,
     * whatever it answered — and where it was not kept, it was not made, and answered nothing.
     */
    @Test
    void anApplicationToEveryValueIsMadePastOnlyTheOnesThatAnswered() {
        Proposition first = Proposition.whereItAnswers(truth(TermPath.of("ad")),
                truth(TermPath.of("as")));
        Proposition second = Proposition.whereItAnswers(truth(TermPath.of("bd")),
                truth(TermPath.of("bs")));
        Proposition kept = truth(TermPath.of("k"));
        List<Proposition> reached = WhereAnApplicationIsMade.reached(List.of(first, second),
                List.of(List.of(kept), List.of()), HowAClosureIsApplied.TO_EVERY_ELEMENT,
                WhereAnApplicationIsMade.nothingAsked());
        assertEquals(kept, reached.get(0));
        assertEquals(Proposition.any(List.of(kept.denied(), truth(TermPath.of("ad")))),
                reached.get(1));
        // Got past by stopping at the first that holds: answered, and not holding.
        List<Proposition> untilOne = WhereAnApplicationIsMade.reached(List.of(first, second),
                List.of(List.of(), List.of()), HowAClosureIsApplied.UNTIL_ONE_HOLDS,
                WhereAnApplicationIsMade.nothingAsked());
        assertEquals(Proposition.all(List.of(truth(TermPath.of("ad")),
                truth(TermPath.of("as")).denied())), untilOne.get(1));
    }
}
