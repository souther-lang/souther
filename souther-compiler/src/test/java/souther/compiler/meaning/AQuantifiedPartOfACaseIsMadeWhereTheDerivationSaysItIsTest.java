package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.semantics.ConditionJoin;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A part of a case that says some element meets a statement is made where the derivation made
 * the statement, as the derivation says it.
 *
 * <p>What a derivation concludes of a quantifier is said once, the denial of the element where
 * it holds as denied, and the cases take it apart as the lines are read ({@link
 * WhereEachLineDecides#lifted}): some element meeting either of two things is some element
 * meeting the one or some element meeting the other, and some element meeting both is one part.
 * Each case here is the conclusion of the derivation so taken apart, with beside it one part some
 * other derivation made, which is told of as one nothing here made: that it says what a quantifier
 * of this one would say with its element taken another way — an atom alone where the quantifier is
 * over both, an atom where the element is denied — is no reason to say it was made here.
 */
class AQuantifiedPartOfACaseIsMadeWhereTheDerivationSaysItIsTest {

    private static final TermPath XS = TermPath.of("xs");
    private static final TermPath YS = TermPath.of("ys");
    private static final DecisionSubject CONTAINER = new DecisionSubject.AnInput(XS);
    private static final DecisionSubject OTHER = new DecisionSubject.AnInput(YS);
    private static final TermPath A = XS.element().then("a");
    private static final TermPath B = XS.element().then("b");

    private static Derivation truthAt(TermPath at) {
        return new Derivation.ATruthOfASubject(new DecisionSubject.AnInput(at), true);
    }

    private static Proposition truth(TermPath at) {
        return new Proposition.Truth(new DecisionSubject.AnInput(at), true);
    }

    private static Derivation some(DecisionSubject container, boolean holds, Derivation element) {
        return new Derivation.SomeElementMeeting(container, element, holds, Optional.empty(),
                HowTheElementsAreAsked.EVERY_ONE);
    }

    /**
     * How many of the parts the cases are taken apart on nothing was found to have made, where
     * the one case is what {@code derived} concludes taken apart as the lines are, with the parts
     * {@code elsewhere} made beside.
     */
    private static int unattributed(Derivation derived, int parts, Proposition... elsewhere) {
        Proposition concluded = derived.concludes(Optional.empty());
        Proposition lifted = WhereEachLineDecides.lifted(concluded);
        List<Proposition> all = new ArrayList<>(List.of(lifted));
        all.addAll(List.of(elsewhere));
        DecidingCase.Cases cases = new DecidingCase.Cases.One(Proposition.all(all));
        CaseExpansion.Attributed made = assertInstanceOf(CaseExpansion.Attributed.class,
                TheChoicesACaseIsMadeOf.of(List.of(cases), List.of(derived)).get(0));
        assertEquals(parts, made.partsSplitOn(), "the parts the case is taken apart on: " + all);
        return made.unattributed();
    }

    @Test
    void someElementMeetingEitherIsMadeWhereItsStatementsWere() {
        Derivation either = some(CONTAINER, true, new Derivation.Joined(ConditionJoin.EITHER,
                truthAt(A), truthAt(B)));
        assertEquals(0, unattributed(either, 1));
    }

    @Test
    void someElementMeetingTheDenialOfEitherIsNotSomeElementMeetingEitherAtAll() {
        Derivation neither = some(CONTAINER, false, new Derivation.Joined(ConditionJoin.EITHER,
                truthAt(A), truthAt(B)));
        Proposition elsewhere = new Proposition.Some(CONTAINER, truth(A), true);
        assertEquals(1, unattributed(neither, 2, elsewhere));
    }

    @Test
    void someElementMeetingBothIsOnePartAndNotOneForEachOfThem() {
        Derivation both = some(CONTAINER, true, new Derivation.Joined(ConditionJoin.BOTH,
                truthAt(A), truthAt(B)));
        Proposition elsewhere = new Proposition.Some(CONTAINER, truth(A), true);
        assertEquals(1, unattributed(both, 2, elsewhere));
    }

    @Test
    void aQuantifierInsideAnotherIsMadeWhereItsStatementsWere() {
        TermPath inner = YS.element().then("c");
        // What no element of the outer container decides leaves whether it holds anything a part.
        Derivation nested = new Derivation.SomeElementMeeting(CONTAINER,
                new Derivation.Joined(ConditionJoin.EITHER, some(OTHER, true, truthAt(inner)),
                        truthAt(B)),
                true, Optional.of(new Derivation.WrittenOut(true)),
                HowTheElementsAreAsked.EVERY_ONE);
        assertEquals(0, unattributed(nested, 2));
    }
}
