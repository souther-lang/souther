package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.TheSignOfAnOrder;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.ConditionJoin;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.semantics.SideAnswered;
import souther.compiler.types.ValueName;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
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
        return new Derivation.ATruthOfASubject(new DecisionSubject.AnInput(at), true);
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
    void aLawStatesWhatItsArgumentsWereReadAsOnTheSideItNames() {
        LawProposition.SomeElement<?> some =
                (LawProposition.SomeElement<?>) lawOf(LIST_ANY, AnswerAspect.TRUTH);
        Derivation meeting = new Derivation.SomeElementMeeting(XS, new Derivation.OnTheSideALawNames(
                (LawProposition.Observed<?>) some.ofTheElement(), truthAt(XS.element())), true,
                Optional.empty());
        Proposition someElement = new Proposition.Some(XS, truth(XS.element()), true);
        assertEquals(some.holds() ? someElement : someElement.denied(),
                concluded(new Derivation.ByALaw(LIST_ANY, AnswerAspect.TRUTH,
                        new Derivation.ALawQuantifies(some, meeting))));
    }

    /**
     * What a law's comparison concludes is the law's own form over what each number it names was
     * read as: {@code List.get} answers something where the index is at or above nought and below
     * the length, and nothing the reading hands in says otherwise.
     */
    @Test
    void aLawsComparisonIsItsOwnFormOverWhatItsNumbersWereReadAs() {
        Derivation read = readingOfGet(INDEX, LENGTH);
        Proposition atOrAboveNought = compared(LinearForm.atom(INDEX), Rel.GE);
        Proposition belowTheLength = compared(new LinearForm<>(ExactRatio.of(-1),
                Map.of(LENGTH, ExactRatio.ONE, INDEX, ExactRatio.of(-1))), Rel.GE);
        assertEquals(Proposition.all(List.of(atOrAboveNought, belowTheLength)),
                concluded(new Derivation.ByALaw(LIST_GET, AnswerAspect.PRESENCE, read)));
    }

    /**
     * A reading of a law's comparison that is not the law's is refused where it is made, however
     * alike its shape: the law's two comparisons at each other's places, a comparison of another
     * law at the law's place, a relation read off the source at the law's place, the right
     * comparison with its numbers read as another number of the law, and a comparison of a choice
     * one of whose cases is not the law's.
     */
    @Test
    void aReadingOfALawsComparisonThatIsNotTheLawsIsRefused() {
        LawProposition.All<?> law = (LawProposition.All<?>) lawOf(LIST_GET, AnswerAspect.PRESENCE);
        LawProposition.Compared<?> first = (LawProposition.Compared<?>) law.parts().get(0);
        LawProposition.Compared<?> second = (LawProposition.Compared<?>) law.parts().get(1);
        LawProposition.Compared<?> another = (LawProposition.Compared<?>) lawOf(STRING_SLICE,
                AnswerAspect.EMPTINESS);
        Derivation ofTheSecond = comparison(second, INDEX, LENGTH);
        Derivation aSourceRelation = new Derivation.AComparisonRead(
                Derivation.ComparisonReading.BY_A_LAW, new Relation.Affine(
                        LinearForm.atom(LENGTH), Rel.GT), false);
        Derivation ofAnother = comparison(another, INDEX, LENGTH);
        Derivation aChoiceOfAnotherCase = new Derivation.AComparisonOfAChoice(
                new Derivation.IfThenElse(truthAt(A), comparison(first, INDEX, LENGTH),
                        aSourceRelation));
        for (Derivation atTheFirst : List.of(ofTheSecond, aSourceRelation, ofAnother,
                aChoiceOfAnotherCase, truthAt(A))) {
            Derivation read = new Derivation.ALawJoins(law, List.of(atTheFirst, ofTheSecond));
            assertThrows(IllegalArgumentException.class,
                    () -> new Derivation.ByALaw(LIST_GET, AnswerAspect.PRESENCE, read),
                    () -> "refused at the first comparison: " + atTheFirst);
        }
        Map<LawNumber<?>, LinearForm<Quantity>> keyedByTheOther = new LinkedHashMap<>();
        second.form().coefs().keySet().forEach(number -> keyedByTheOther.put(number,
                LinearForm.atom(INDEX)));
        assertThrows(IllegalArgumentException.class, () -> Derivation.ALawComparison.of(first,
                keyedByTheOther, Map.of()));
        // And a choice each of whose cases is the law's comparison, or stopped, is a reading.
        Derivation aChoiceOfTheLaws = new Derivation.AComparisonOfAChoice(
                new Derivation.IfThenElse(truthAt(A), comparison(first, INDEX, LENGTH),
                        new Derivation.Stopped(new WhyUnread.NotMetByTheReading(), false)));
        new Derivation.ByALaw(LIST_GET, AnswerAspect.PRESENCE,
                new Derivation.ALawJoins(law, List.of(aChoiceOfTheLaws, ofTheSecond)));
    }

    /**
     * A reading of what a law states of some element, or of a side, that is not the law's is
     * refused: the quantifier of another law, an element read as another side, two values read
     * under a sameness the law does not state — and a part the reading stopped at is said wherever
     * it stands.
     */
    @Test
    void aReadingOfALawsElementsOrSidesThatIsNotTheLawsIsRefused() {
        LawProposition.SomeElement<?> any =
                (LawProposition.SomeElement<?>) lawOf(LIST_ANY, AnswerAspect.TRUTH);
        LawProposition.SomeElement<?> contains =
                (LawProposition.SomeElement<?>) lawOf(SET_CONTAINS, AnswerAspect.TRUTH);
        LawProposition.Observed<?> closureTrue = (LawProposition.Observed<?>) any.ofTheElement();
        LawProposition.Observed<?> closureFalse = new LawProposition.Observed<>(
                closureTrue.of(), new SideAnswered(closureTrue.side().aspect(),
                        !closureTrue.side().holds()));
        Derivation readAsTheOtherSide = new Derivation.SomeElementMeeting(XS,
                new Derivation.OnTheSideALawNames(closureFalse, truthAt(XS.element())), true,
                Optional.empty());
        Derivation readAsTheLawsSide = new Derivation.SomeElementMeeting(XS,
                new Derivation.OnTheSideALawNames(closureTrue, truthAt(XS.element())), true,
                Optional.empty());
        for (Derivation notOfIt : List.of(
                new Derivation.ALawQuantifies(theOtherWay(any), readAsTheLawsSide),
                new Derivation.ALawQuantifies(contains, readAsTheOtherSide),
                new Derivation.ALawQuantifies(any, readAsTheOtherSide),
                new Derivation.ALawQuantifies(any, truthAt(XS.element())),
                truthAt(XS.element()))) {
            assertThrows(IllegalArgumentException.class, () -> new Derivation.ByALaw(LIST_ANY,
                    AnswerAspect.TRUTH, notOfIt), () -> "refused: " + notOfIt);
        }
        LawProposition.Same<?> same = (LawProposition.Same<?>) contains.ofTheElement();
        LawProposition.Same<?> notSame = theOtherWay(same);
        assertThrows(IllegalArgumentException.class, () -> new Derivation.ByALaw(SET_CONTAINS,
                AnswerAspect.TRUTH, new Derivation.ALawQuantifies(contains,
                        new Derivation.SomeElementMeeting(XS, new Derivation.TheSameValue(notSame,
                                new DecisionSubject.AnInput(XS.element()),
                                new DecisionSubject.AnInput(A)), true, Optional.empty()))));
        new Derivation.ByALaw(SET_CONTAINS, AnswerAspect.TRUTH, new Derivation.ALawQuantifies(
                contains, new Derivation.SomeElementMeeting(XS, new Derivation.TheSameValue(same,
                        new DecisionSubject.AnInput(XS.element()), new DecisionSubject.AnInput(A)),
                        true, Optional.empty())));
        new Derivation.ByALaw(LIST_ANY, AnswerAspect.TRUTH, new Derivation.ALawQuantifies(any,
                new Derivation.Stopped(new WhyUnread.NotMetByTheReading(), false)));
    }

    /** A law is the one the library settles the side by: a side no law settles has none to read. */
    @Test
    void aLawIsTheOneTheLibrarySettlesTheSideBy() {
        assertThrows(IllegalArgumentException.class, () -> new Derivation.ByALaw(STRING_CONTAINS,
                AnswerAspect.TRUTH, new Derivation.Stopped(new WhyUnread.NotMetByTheReading(),
                        false)));
        assertThrows(IllegalArgumentException.class, () -> new Derivation.ByALaw(LIST_ANY,
                AnswerAspect.PRESENCE, new Derivation.Stopped(new WhyUnread.NotMetByTheReading(),
                        false)));
    }

    /**
     * The cases a size or a definition is read in are the library's: one arm for each, and an
     * arm of a size taken under a reading of its case.
     */
    @Test
    void theCasesAStepIsReadInAreTheLibrarys() {
        Derivation.MatchArms.Arm arm = new Derivation.MatchArms.Arm(truthAt(A), truthAt(B));
        assertThrows(IllegalArgumentException.class, () -> new Derivation.AnOperationsCases(
                INT_MIN, List.of(arm)));
        new Derivation.AnOperationsCases(INT_MIN, List.of(arm, arm));
        assertThrows(IllegalArgumentException.class, () -> new Derivation.ASizeInCases(
                SET_INSERT, List.of(arm)));
        assertThrows(IllegalArgumentException.class, () -> new Derivation.ASizeInCases(
                SET_INSERT, List.of(arm, arm)));
        Derivation.MatchArms.Arm stopped = new Derivation.MatchArms.Arm(new Derivation.Stopped(
                new WhyUnread.NotMetByTheReading(), false), truthAt(B));
        new Derivation.ASizeInCases(SET_INSERT, List.of(stopped, stopped));
    }

    /**
     * A sign an order answered, compared with a number, is the comparison of the arguments it is
     * the order of; and one every answer comes out the same against is that answer, worked out
     * from the bounds of what the operation answers — so neither step is made of the other's
     * comparison.
     */
    @Test
    void aSignOfAnOrderStatesWhatItsArgumentsDoOrWhatItsBoundsSettle() {
        TheSignOfAnOrder.TheSign aboveNought = new TheSignOfAnOrder.TheSign(INT_COMPARE,
                Granularity.DISCRETE, Rel.GT, ExactRatio.ZERO);
        TheSignOfAnOrder.TheSign aboveOne = new TheSignOfAnOrder.TheSign(INT_COMPARE,
                Granularity.DISCRETE, Rel.GT, ExactRatio.ONE);
        TheSignOfAnOrder.TheSign atOrAboveLessOne = new TheSignOfAnOrder.TheSign(INT_COMPARE,
                Granularity.DISCRETE, Rel.GE, ExactRatio.of(-1));
        assertEquals(truth(A), concluded(new Derivation.AnOrderOfItsArguments(aboveNought,
                truthAt(A))));
        assertEquals(new Proposition.Always(false),
                concluded(new Derivation.ASignItsBoundsSettle(aboveOne)));
        assertEquals(new Proposition.Always(true),
                concluded(new Derivation.ASignItsBoundsSettle(atOrAboveLessOne)));
        assertThrows(IllegalArgumentException.class,
                () -> new Derivation.ASignItsBoundsSettle(aboveNought));
        assertThrows(IllegalArgumentException.class,
                () -> new Derivation.AnOrderOfItsArguments(aboveOne, truthAt(A)));
    }

    private static final ValueName.Stdlib LIST_ANY = new ValueName.Stdlib.Operation("List", "any");
    private static final ValueName.Stdlib LIST_GET = new ValueName.Stdlib.Operation("List", "get");
    private static final ValueName.Stdlib SET_CONTAINS =
            new ValueName.Stdlib.Operation("Set", "contains");
    private static final ValueName.Stdlib SET_INSERT =
            new ValueName.Stdlib.Operation("Set", "insert");
    private static final ValueName.Stdlib STRING_CONTAINS =
            new ValueName.Stdlib.Operation("String", "contains");
    private static final ValueName.Stdlib STRING_SLICE =
            new ValueName.Stdlib.Operation("String", "slice");
    private static final ValueName.Stdlib INT_MIN = new ValueName.Stdlib.Operation("Int", "min");
    private static final ValueName.Stdlib INT_COMPARE =
            new ValueName.Stdlib.Operation("Int", "compare");

    /** Two quantities standing for what a number of a law was read as. */
    private static final Quantity INDEX = new Quantity.HowManyDifferent(A, A.element());
    private static final Quantity LENGTH = new Quantity.HowManyDifferent(B, B.element());

    /** The statement the law the library settles {@code aspect} of {@code operation} by makes. */
    private static LawProposition<?> lawOf(ValueName.Stdlib operation, AnswerAspect aspect) {
        BoundOperationFacts.Settled settled = DefaultBoundOperationFacts.get().settled(operation,
                OperationLaw.Observed.of(aspect));
        return ((OperationLaw.Observation<?>) ((BoundOperationFacts.Settled.ByALaw) settled)
                .law()).equivalentTo();
    }

    /** {@code List.get}'s law, with the index read as {@code index} and the list's length as
     *  {@code length}. */
    private static Derivation readingOfGet(Quantity index, Quantity length) {
        LawProposition.All<?> law = (LawProposition.All<?>) lawOf(LIST_GET, AnswerAspect.PRESENCE);
        return new Derivation.ALawJoins(law, List.of(
                comparison((LawProposition.Compared<?>) law.parts().get(0), index, length),
                comparison((LawProposition.Compared<?>) law.parts().get(1), index, length)));
    }

    /** {@code part}, with the number of an argument read as {@code index} and a size as
     *  {@code length}. */
    private static Derivation comparison(LawProposition.Compared<?> part, Quantity index,
                                         Quantity length) {
        Map<LawNumber<?>, LinearForm<Quantity>> numbers = new LinkedHashMap<>();
        part.form().coefs().keySet().forEach(number -> numbers.put(number, LinearForm.atom(
                number instanceof LawNumber.SizeOf<?> ? length : index)));
        return Derivation.ALawComparison.of(part, numbers, Map.of());
    }

    /** The sameness {@code same} states, said the other way. */
    private static <A> LawProposition.Same<A> theOtherWay(LawProposition.Same<A> same) {
        return new LawProposition.Same<>(same.one(), same.other(), !same.holds());
    }

    /** Some element meeting what {@code some} states of it, said the other way. */
    private static <A> LawProposition.SomeElement<A> theOtherWay(
            LawProposition.SomeElement<A> some) {
        return new LawProposition.SomeElement<>(some.container(), some.ofTheElement(),
                !some.holds());
    }

    /** {@code form states 0}, as a comparison concludes it. */
    private static Proposition compared(LinearForm<Quantity> form, Rel states) {
        Relation.OneWay<Quantity> one = Relation.OneWay.of(form, states);
        return Proposition.compared(new Relation.Affine(one.form(), one.proposition()),
                one.holds());
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
