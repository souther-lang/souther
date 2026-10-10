package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.DeclaredArgument;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.ScopedDeclarations;
import souther.compiler.check.Symbols;
import souther.compiler.check.TheSignOfAnOrder;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.ConditionJoin;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.semantics.SideAnswered;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.HashMap;
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
    private static final TermPath YS = TermPath.of("ys");

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
                concluded(new Derivation.ByALaw(callOf(LIST_ANY, some.container(), XS),
                        AnswerAspect.TRUTH, new Derivation.ALawQuantifies(some, meeting))));
    }

    /**
     * A reading that holds the law's own part and has the container read at another argument's
     * position is refused: the quantifier over {@code ys} is no reading of what {@code List.any}
     * states of {@code xs}. What the closure states of an element is the closure's, which may
     * name any position, and is held to none.
     */
    @Test
    void aReadingOfALawPartAtAnotherContainerThanTheCallsIsRefused() {
        LawProposition.SomeElement<?> some =
                (LawProposition.SomeElement<?>) lawOf(LIST_ANY, AnswerAspect.TRUTH);
        LawProposition.Observed<?> observed = (LawProposition.Observed<?>) some.ofTheElement();
        Derivation.TheCall call = callOf(LIST_ANY, some.container(), XS);
        Derivation overOtherElements = new Derivation.SomeElementMeeting(YS,
                new Derivation.OnTheSideALawNames(observed, truthAt(YS.element())), true,
                Optional.empty());
        assertThrows(IllegalArgumentException.class, () -> new Derivation.ByALaw(call,
                AnswerAspect.TRUTH, new Derivation.ALawQuantifies(some, overOtherElements)));
        // The call's own container, and an argument that stands at no position, are readings.
        new Derivation.ByALaw(call, AnswerAspect.TRUTH, new Derivation.ALawQuantifies(some,
                new Derivation.SomeElementMeeting(XS, new Derivation.OnTheSideALawNames(observed,
                        truthAt(XS.element())), true, Optional.empty())));
        new Derivation.ByALaw(new Derivation.TheCall(LIST_ANY, Map.of()), AnswerAspect.TRUTH,
                new Derivation.ALawQuantifies(some, overOtherElements));
    }

    /**
     * A side observed of an argument is observed of the position the call has it at:
     * {@code Option.map} answers something where its argument does, and that is no reading of
     * the argument standing at another position.
     */
    @Test
    void aSideObservedAtAnotherPositionThanTheCallsIsRefused() {
        LawProposition.Observed<?> law =
                (LawProposition.Observed<?>) lawOf(OPTION_MAP, AnswerAspect.PRESENCE);
        Derivation.TheCall call = callOf(OPTION_MAP,
                ((LawSubject.Argument<?>) law.of()).argument(), XS);
        new Derivation.ByALaw(call, AnswerAspect.PRESENCE, new Derivation.OnTheSideALawNames(
                law, new Derivation.PresentInASubject(new DecisionSubject.AnInput(XS))));
        // Of the argument itself and of what the law observes of it: not another position, not a
        // position inside it, not another thing observed of it.
        for (Derivation notOfIt : List.of(
                new Derivation.PresentInASubject(new DecisionSubject.AnInput(YS)),
                new Derivation.PresentInASubject(new DecisionSubject.AnInput(XS.element())),
                truthAt(XS))) {
            assertThrows(IllegalArgumentException.class, () -> new Derivation.ByALaw(call,
                    AnswerAspect.PRESENCE, new Derivation.OnTheSideALawNames(law, notOfIt)),
                    () -> "refused: " + notOfIt);
        }
    }

    /**
     * A reading that holds the law's own comparison and has an argument's number read as another
     * argument's is refused: {@code List.get}'s index read as the list's length, or its length as
     * the index, is no reading of what it states of the call.
     */
    @Test
    void aReadingOfALawsNumbersAtOtherArgumentsThanTheCallsIsRefused() {
        Derivation.TheCall call = callOfGet();
        new Derivation.ByALaw(call, AnswerAspect.PRESENCE, readingOfGet(INDEX, LENGTH));
        for (Derivation swapped : List.of(readingOfGet(LENGTH, INDEX),
                readingOfGet(INDEX, INDEX), readingOfGet(LENGTH, LENGTH))) {
            assertThrows(IllegalArgumentException.class, () -> new Derivation.ByALaw(call,
                    AnswerAspect.PRESENCE, swapped), () -> "refused: " + swapped);
        }
    }

    /**
     * A reading that has an argument's number at the argument's own position and as a number of
     * another kind is refused: {@code List.get}'s length read as how many different values the
     * list's elements come to, which is fewer where two are the same, or as the list's elements
     * counted, or the index read as that count of its own position.
     */
    @Test
    void aReadingOfANumberOfAnotherKindThanTheLawsIsRefused() {
        Derivation.TheCall call = callOfGet();
        Quantity differentInTheList = new Quantity.HowManyDifferent(B, B.element());
        Quantity metInTheList = new Quantity.HowManyMeet(B, truth(B.element()));
        Quantity differentAtTheIndex = new Quantity.HowManyDifferent(A, A.element());
        for (Derivation ofAnotherKind : List.of(readingOfGet(INDEX, differentInTheList),
                readingOfGet(INDEX, metInTheList), readingOfGet(differentAtTheIndex, LENGTH))) {
            assertThrows(IllegalArgumentException.class, () -> new Derivation.ByALaw(call,
                    AnswerAspect.PRESENCE, ofAnotherKind), () -> "refused: " + ofAnotherKind);
        }
    }

    /**
     * Two values read as a sameness the law states are the call's: the element at one position and
     * the argument at another, and neither read at the other's.
     */
    @Test
    void aSamenessReadAtOtherPositionsThanTheCallsIsRefused() {
        LawProposition.SomeElement<?> contains =
                (LawProposition.SomeElement<?>) lawOf(SET_CONTAINS, AnswerAspect.TRUTH);
        LawProposition.Same<?> same = (LawProposition.Same<?>) contains.ofTheElement();
        Derivation.TheCall call = callOf(SET_CONTAINS, contains.container(), XS,
                ((LawSubject.Argument<?>) same.other()).argument(), A);
        for (DecisionSubject[] read : List.of(
                new DecisionSubject[] {new DecisionSubject.AnInput(YS.element()),
                        new DecisionSubject.AnInput(A)},
                new DecisionSubject[] {new DecisionSubject.AnInput(XS.element()),
                        new DecisionSubject.AnInput(B)},
                new DecisionSubject[] {new DecisionSubject.AnInput(A),
                        new DecisionSubject.AnInput(XS.element())})) {
            assertThrows(IllegalArgumentException.class, () -> new Derivation.ByALaw(call,
                    AnswerAspect.TRUTH, new Derivation.ALawQuantifies(contains,
                            new Derivation.SomeElementMeeting(XS, new Derivation.TheSameValue(same,
                                    read[0], read[1]), true, Optional.empty()))));
        }
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
                concluded(new Derivation.ByALaw(callOfGet(), AnswerAspect.PRESENCE, read)));
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
                    () -> new Derivation.ByALaw(callOfGet(), AnswerAspect.PRESENCE, read),
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
        new Derivation.ByALaw(callOfGet(), AnswerAspect.PRESENCE,
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
            assertThrows(IllegalArgumentException.class, () -> new Derivation.ByALaw(
                    callOf(LIST_ANY, any.container(), XS), AnswerAspect.TRUTH, notOfIt),
                    () -> "refused: " + notOfIt);
        }
        LawProposition.Same<?> same = (LawProposition.Same<?>) contains.ofTheElement();
        LawProposition.Same<?> notSame = theOtherWay(same);
        Derivation.TheCall containsXs = callOf(SET_CONTAINS, contains.container(), XS,
                ((LawSubject.Argument<?>) same.other()).argument(), A);
        assertThrows(IllegalArgumentException.class, () -> new Derivation.ByALaw(containsXs,
                AnswerAspect.TRUTH, new Derivation.ALawQuantifies(contains,
                        new Derivation.SomeElementMeeting(XS, new Derivation.TheSameValue(notSame,
                                new DecisionSubject.AnInput(XS.element()),
                                new DecisionSubject.AnInput(A)), true, Optional.empty()))));
        new Derivation.ByALaw(containsXs, AnswerAspect.TRUTH, new Derivation.ALawQuantifies(
                contains, new Derivation.SomeElementMeeting(XS, new Derivation.TheSameValue(same,
                        new DecisionSubject.AnInput(XS.element()), new DecisionSubject.AnInput(A)),
                        true, Optional.empty())));
        new Derivation.ByALaw(callOf(LIST_ANY, any.container(), XS), AnswerAspect.TRUTH,
                new Derivation.ALawQuantifies(any,
                        new Derivation.Stopped(new WhyUnread.NotMetByTheReading(), false)));
    }

    /** A law is the one the library settles the side by: a side no law settles has none to read. */
    @Test
    void aLawIsTheOneTheLibrarySettlesTheSideBy() {
        assertThrows(IllegalArgumentException.class, () -> new Derivation.ByALaw(
                new Derivation.TheCall(STRING_CONTAINS, Map.of()), AnswerAspect.TRUTH,
                new Derivation.Stopped(new WhyUnread.NotMetByTheReading(), false)));
        assertThrows(IllegalArgumentException.class, () -> new Derivation.ByALaw(
                new Derivation.TheCall(LIST_ANY, Map.of()), AnswerAspect.PRESENCE,
                new Derivation.Stopped(new WhyUnread.NotMetByTheReading(), false)));
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
        Derivation.TheCall insert = new Derivation.TheCall(SET_INSERT, Map.of());
        assertThrows(IllegalArgumentException.class, () -> new Derivation.ASizeInCases(
                insert, List.of(arm)));
        assertThrows(IllegalArgumentException.class, () -> new Derivation.ASizeInCases(
                insert, List.of(arm, arm)));
        Derivation.MatchArms.Arm stopped = new Derivation.MatchArms.Arm(new Derivation.Stopped(
                new WhyUnread.NotMetByTheReading(), false), truthAt(B));
        new Derivation.ASizeInCases(insert, List.of(stopped, stopped));
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
        List<DeclaredArgument> ordered = TheSignOfAnOrder.orderedArguments(INT_COMPARE);
        Derivation.TheCall compare = callOf(INT_COMPARE, ordered.get(0), A, ordered.get(1), B);
        Derivation greaterThanTheLesser = relationOf(NUMBER_AT_A, NUMBER_AT_B, Rel.GT);
        assertEquals(concluded(greaterThanTheLesser), concluded(
                new Derivation.AnOrderOfItsArguments(compare, aboveNought, greaterThanTheLesser)));
        // The greater against the lesser as the sign says, and no other statement of them: not
        // the other way round, not the other relation, not either against nought, not a number
        // of the same position of another kind.
        for (Derivation notTheOrder : List.of(
                relationOf(NUMBER_AT_A, NUMBER_AT_B, Rel.LT),
                relationOf(NUMBER_AT_A, NUMBER_AT_B, Rel.GE),
                relationOf(NUMBER_AT_B, NUMBER_AT_A, Rel.GT),
                new Derivation.AComparisonRead(Derivation.ComparisonReading.BY_A_LAW,
                        new Relation.Affine(LinearForm.atom(NUMBER_AT_A), Rel.GT), true),
                relationOf(NUMBER_AT_A, LENGTH, Rel.GT),
                truthAt(A))) {
            assertThrows(IllegalArgumentException.class, () -> new Derivation.AnOrderOfItsArguments(
                    compare, aboveNought, notTheOrder), () -> "refused: " + notTheOrder);
        }
        assertEquals(new Proposition.Always(false),
                concluded(new Derivation.ASignItsBoundsSettle(aboveOne)));
        assertEquals(new Proposition.Always(true),
                concluded(new Derivation.ASignItsBoundsSettle(atOrAboveLessOne)));
        assertThrows(IllegalArgumentException.class,
                () -> new Derivation.ASignItsBoundsSettle(aboveNought));
        assertThrows(IllegalArgumentException.class, () -> new Derivation.AnOrderOfItsArguments(
                compare, aboveOne, greaterThanTheLesser));
    }

    /** {@code first - second states 0}, read as a comparison of the numbers it is over. */
    private static Derivation relationOf(Quantity first, Quantity second, Rel states) {
        Relation.OneWay<Quantity> one = Relation.OneWay.of(new LinearForm<>(ExactRatio.ZERO,
                Map.of(first, ExactRatio.ONE, second, ExactRatio.of(-1))), states);
        return new Derivation.AComparisonRead(Derivation.ComparisonReading.BY_A_LAW,
                new Relation.Affine(one.form(), one.proposition()), one.holds());
    }

    private static final ValueName.Stdlib LIST_ANY = new ValueName.Stdlib.Operation("List", "any");
    private static final ValueName.Stdlib LIST_GET = new ValueName.Stdlib.Operation("List", "get");
    private static final ValueName.Stdlib OPTION_MAP =
            new ValueName.Stdlib.Operation("Option", "map");
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
    private static final Symbols SYMBOLS = Symbols.none(DefaultStdlib.get());
    private static final ValueName.Stdlib LIST_LENGTH =
            new ValueName.Stdlib.Operation("List", "length");
    private static final Quantity NUMBER_AT_A =
            new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(A));
    private static final Quantity NUMBER_AT_B =
            new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(B));
    private static final Quantity INDEX = NUMBER_AT_A;
    private static final Quantity LENGTH = new DecisionAtom.OfTheInput(NumericTerm.TakenOf.of(
            LIST_LENGTH, B, Type.list(Type.INT), ScopedDeclarations.wrapsOf(SYMBOLS), SYMBOLS));

    /** A call of {@code operation} with the argument {@code argument} of its law at {@code at}. */
    private static Derivation.TheCall callOf(ValueName.Stdlib operation, Object argument,
                                             TermPath at) {
        return new Derivation.TheCall(operation, Map.of((DeclaredArgument) argument, at));
    }

    /** A call of {@code operation} with two arguments of its law each at a position. */
    private static Derivation.TheCall callOf(ValueName.Stdlib operation, Object argument,
                                             TermPath at, Object other, TermPath otherAt) {
        return new Derivation.TheCall(operation, Map.of((DeclaredArgument) argument, at,
                (DeclaredArgument) other, otherAt));
    }

    /** A call of {@code List.get} with the index at {@code a} and the list at {@code b}. */
    private static Derivation.TheCall callOfGet() {
        LawProposition.All<?> law = (LawProposition.All<?>) lawOf(LIST_GET, AnswerAspect.PRESENCE);
        Map<DeclaredArgument, TermPath> standingAt = new HashMap<>();
        for (LawProposition<?> part : law.parts()) {
            for (LawNumber<?> number : ((LawProposition.Compared<?>) part).form().coefs()
                    .keySet()) {
                switch (number) {
                    case LawNumber.AnArgument<?> index ->
                            standingAt.put((DeclaredArgument) index.argument(), A);
                    case LawNumber.SizeOf<?> size -> standingAt.put((DeclaredArgument)
                            ((LawSubject.Argument<?>) size.of()).argument(), B);
                    default -> throw new IllegalStateException("List.get's law names " + number);
                }
            }
        }
        return new Derivation.TheCall(LIST_GET, standingAt);
    }

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
