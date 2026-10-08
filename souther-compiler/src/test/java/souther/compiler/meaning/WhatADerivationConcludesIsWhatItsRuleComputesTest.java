package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.ConditionJoin;
import souther.compiler.semantics.SideAnswered;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Each rule concludes what its own semantics says of what its premises conclude, and the parts
 * nothing read are numbered in the order a reading meets them.
 *
 * <p>Asked of derivations built by hand, so each rule is held to its sentence and not to whatever a
 * reading of a model happens to hand it.
 */
class WhatADerivationConcludesIsWhatItsRuleComputesTest {

    private static final TermPath A = TermPath.of("a");
    private static final TermPath B = TermPath.of("b");
    private static final TermPath C = TermPath.of("c");
    private static final TermPath XS = TermPath.of("xs");

    private static Derivation truthAt(TermPath at) {
        return new Derivation.ATruthAtAPosition(at, true);
    }

    private static Proposition truth(TermPath at) {
        return new Proposition.Truth(new DecisionSubject.AnInput(at), true);
    }

    private static Proposition concluded(Derivation derivation) {
        return derivation.concludes(Optional.empty());
    }

    @Test
    void anIfIsItsArmUnderItsConditionAndItsOtherArmUnderTheDenial() {
        assertEquals(Proposition.any(List.of(
                        Proposition.all(List.of(truth(A), truth(B))),
                        Proposition.all(List.of(truth(A).denied(), truth(C))))),
                concluded(new Derivation.IfThenElse(truthAt(A), truthAt(B), truthAt(C))));
    }

    @Test
    void aJoinIsBothOrEitherOfItsHalves() {
        assertEquals(Proposition.all(List.of(truth(A), truth(B))),
                concluded(new Derivation.Joined(ConditionJoin.BOTH, truthAt(A), truthAt(B))));
        assertEquals(Proposition.any(List.of(truth(A), truth(B))),
                concluded(new Derivation.Joined(ConditionJoin.EITHER, truthAt(A), truthAt(B))));
    }

    @Test
    void aDenialIsWhatIsUnderItTheOtherWayRoundOnlyWhereItDenies() {
        assertEquals(truth(A).denied(), concluded(new Derivation.UnderADenial(truthAt(A), true)));
        assertEquals(truth(A), concluded(new Derivation.UnderADenial(truthAt(A), false)));
    }

    @Test
    void anArmIsTakenWhereItSelectsAndNoArmBeforeItDoes() {
        Derivation first = new Derivation.UnderADenial(truthAt(A), false);
        Derivation selectsB = truthAt(B);
        Proposition stated = concluded(new Derivation.MatchArms(List.of(
                new Derivation.MatchArms.Arm(first, truthAt(C)),
                new Derivation.MatchArms.Arm(selectsB, new Derivation.WrittenOut(true)))));
        assertEquals(Proposition.any(List.of(
                Proposition.all(List.of(truth(A), truth(C))),
                Proposition.all(List.of(truth(A).denied(), truth(B))))), stated);
    }

    @Test
    void aWitnessLawStatesSomeElementOrItsDenialAsTheLawSays() {
        Derivation some = new Derivation.SomeElementMeeting(XS, truthAt(XS.element()), true,
                Optional.empty());
        Proposition someElement = new Proposition.Some(XS, truth(XS.element()), true);
        ValueName.Stdlib any = new ValueName.Stdlib.Operation("List", "any");
        assertEquals(someElement, concluded(new Derivation.AWitnessLaw(any,
                new SideAnswered(AnswerAspect.TRUTH, true), some)));
        assertEquals(someElement.denied(), concluded(new Derivation.AWitnessLaw(any,
                new SideAnswered(AnswerAspect.TRUTH, false), some)));
    }

    /**
     * What no element decides comes out of the quantifier, and whether the container holds anything
     * is a part only where the conclusion has it as one.
     */
    @Test
    void whatNoElementDecidesIsTakenOutOfTheQuantifier() {
        Derivation size = new Derivation.WrittenOut(true);
        Derivation both = new Derivation.Joined(ConditionJoin.BOTH, truthAt(XS.element()),
                truthAt(A));
        assertEquals(Proposition.all(List.of(truth(A),
                        new Proposition.Some(XS, truth(XS.element()), true))),
                concluded(new Derivation.SomeElementMeeting(XS, both, true, Optional.empty())));
        assertEquals(truth(A), concluded(new Derivation.SomeElementMeeting(XS, truthAt(A), true,
                Optional.of(size))));
        assertEquals(true, Derivation.SomeElementMeeting.asksWhetherItHoldsAnything(XS, truth(A)));
        assertEquals(false, Derivation.SomeElementMeeting.asksWhetherItHoldsAnything(XS,
                Proposition.all(List.of(truth(A), truth(XS.element())))));
    }

    /** A conclusion that has the container's holding anything as a part cannot be made without it. */
    @Test
    void aPartTheConclusionHasMustHaveBeenRead() {
        assertThrows(IllegalStateException.class, () -> concluded(
                new Derivation.SomeElementMeeting(XS, truthAt(A), true, Optional.empty())));
    }

    /**
     * Parts nothing read are numbered in the order a reading meets them: an {@code if}'s condition,
     * then its arm, then its other arm.
     */
    @Test
    void thePartsNothingReadAreNumberedInTheOrderTheyAreMet() {
        WhyUnread why = new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.SUBJECT);
        Derivation stated = new Derivation.IfThenElse(new Derivation.Stopped(why, false),
                new Derivation.Stopped(why, false), new Derivation.Stopped(why, false));
        Proposition first = new Proposition.Unread(Optional.empty(), 0, why, false, true);
        Proposition second = new Proposition.Unread(Optional.empty(), 1, why, false, true);
        Proposition third = new Proposition.Unread(Optional.empty(), 2, why, false, true);
        assertEquals(Proposition.any(List.of(Proposition.all(List.of(first, second)),
                Proposition.all(List.of(first.denied(), third)))), concluded(stated));
    }

    /** A part met twice is two parts: each concluding of a step that stopped is a part of its own. */
    @Test
    void oneConclusionNumbersEachStopItMeets() {
        WhyUnread why = new WhyUnread.NoMeasureOfItsSize();
        Conclusion conclusion = new Conclusion(Optional.empty());
        Derivation.Stopped stopped = new Derivation.Stopped(why, true);
        Proposition stated = conclusion.of(new Derivation.Joined(ConditionJoin.EITHER, stopped,
                new Derivation.Stopped(why, true)));
        assertEquals(Proposition.any(List.of(
                new Proposition.Unread(Optional.empty(), 0, why, true, true),
                new Proposition.Unread(Optional.empty(), 1, why, true, true))), stated);
        assertEquals(new Proposition.Unread(Optional.empty(), 0, why, true, true),
                conclusion.concludedAt(stopped));
    }
}
