package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.Case;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * The cases an arm is chosen by are taken away from it only where the statement is the arms of
 * one choice and each arm's relation stands only where its cases hold: the cases of one subject,
 * no two of which share a case, and a place of the relation that is there under those cases and
 * no wider ones. A relation that reads nothing the cases narrow is read over every row that gets
 * to it, and says nothing of where it is the statement.
 */
class TheArmsOfAChoiceAreTheRelationsBesideCasesThatKeepThemApartTest {

    private static final TermPath CHOSEN = TermPath.of("chosen");
    private static final TermPath OUTSIDE = TermPath.of("outside");

    @Test
    void armsWhoseCasesShareNoneAreEachTheRelationBesideThem() {
        Proposition inA = sameUnder(CHOSEN, "A");
        Proposition inBC = sameUnder(CHOSEN, "B", "C");
        Proposition stated = Proposition.any(List.of(
                Proposition.all(List.of(inCases(CHOSEN, "A"), inA)),
                Proposition.all(List.of(inCases(CHOSEN, "B", "C"), inBC))));
        assertEquals(List.of(inA, inBC), Cutting.armsOfAChoice(stated));
    }

    /** The cases of the arms need not cover the subject: the rest are rows the statement is false
     *  at, and each relation stands only under the cases it is chosen by. */
    @Test
    void armsThatDoNotCoverEveryCaseAreStillTheArmsOfAChoice() {
        Proposition inA = sameUnder(CHOSEN, "A");
        Proposition inB = sameUnder(CHOSEN, "B");
        Proposition stated = Proposition.any(List.of(
                Proposition.all(List.of(inCases(CHOSEN, "A"), inA)),
                Proposition.all(List.of(inCases(CHOSEN, "B"), inB))));
        assertEquals(List.of(inA, inB), Cutting.armsOfAChoice(stated));
    }

    /** A relation over places the cases do not narrow is the same relation in every arm, and
     *  nothing says it is the statement only where its cases hold. */
    @Test
    void aRelationThatStandsWhereverTheCasesDoNotHoldIsNotTheArmsToo() {
        Proposition everywhere = sameAt(OUTSIDE, TermPath.of("other"));
        Proposition stated = Proposition.any(List.of(
                Proposition.all(List.of(inCases(CHOSEN, "A"), everywhere)),
                Proposition.all(List.of(inCases(CHOSEN, "B"), sameAt(OUTSIDE, TermPath.of("o2"))))));
        assertNull(Cutting.armsOfAChoice(stated));
    }

    /** Narrowed to the other arm's cases, a place is no place of this arm. */
    @Test
    void aRelationUnderOtherCasesThanItsArmsIsNotItsArm() {
        Proposition stated = Proposition.any(List.of(
                Proposition.all(List.of(inCases(CHOSEN, "A"), sameUnder(CHOSEN, "B"))),
                Proposition.all(List.of(inCases(CHOSEN, "B"), sameUnder(CHOSEN, "A")))));
        assertNull(Cutting.armsOfAChoice(stated));
    }

    @Test
    void armsThatMayBothHoldAreNotTheArmsOfAChoice() {
        Proposition stated = Proposition.any(List.of(
                Proposition.all(List.of(inCases(CHOSEN, "A", "B"), sameUnder(CHOSEN, "A", "B"))),
                Proposition.all(List.of(inCases(CHOSEN, "B", "C"), sameUnder(CHOSEN, "B", "C")))));
        assertNull(Cutting.armsOfAChoice(stated));
    }

    @Test
    void armsChosenOnTwoSubjectsAreNotTheArmsOfOneChoice() {
        TermPath other = TermPath.of("other");
        Proposition stated = Proposition.any(List.of(
                Proposition.all(List.of(inCases(CHOSEN, "A"), sameUnder(CHOSEN, "A"))),
                Proposition.all(List.of(inCases(other, "B"), sameUnder(other, "B")))));
        assertNull(Cutting.armsOfAChoice(stated));
    }

    /** What a model writes with a flag instead of a match is no choice by cases: nothing of it is
     *  taken away, whatever it comes to. */
    @Test
    void aFlagWrittenInPlaceOfCasesIsNoChoiceByCases() {
        Proposition flag = new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of("flag")),
                true);
        Proposition stated = Proposition.any(List.of(
                Proposition.all(List.of(flag, sameUnder(CHOSEN, "A"))),
                Proposition.all(List.of(flag.denied(), sameUnder(CHOSEN, "B")))));
        assertNull(Cutting.armsOfAChoice(stated));
    }

    @Test
    void anArmStatingMoreThanOneRelationIsNotReadAsOne() {
        Proposition stated = Proposition.any(List.of(
                Proposition.all(List.of(inCases(CHOSEN, "A"), sameUnder(CHOSEN, "A"),
                        sameAt(OUTSIDE, TermPath.of("x")))),
                Proposition.all(List.of(inCases(CHOSEN, "B"), sameUnder(CHOSEN, "B")))));
        assertNull(Cutting.armsOfAChoice(stated));
    }

    private static CasesLeft casesOf(String... leaves) {
        List<Refinement> atoms = new ArrayList<>();
        for (String leaf : leaves) {
            TypeSymbol symbol = TypeSymbols.declared(new TypeKey("probe", leaf));
            atoms.add(Refinement.of(new Case.SumCase(symbol, true)));
        }
        return CasesLeft.ofEach(atoms);
    }

    /** The value at {@code of} being one of {@code leaves}. */
    private static Proposition inCases(TermPath of, String... leaves) {
        return new Proposition.InCases(new DecisionSubject.AnInput(of), casesOf(leaves), true);
    }

    /** Two values being one, the first at a place that is there under {@code leaves} of
     *  {@code of} alone. */
    private static Proposition sameUnder(TermPath of, String... leaves) {
        return sameAt(of.refine(casesOf(leaves)).then("x"), TermPath.of("y"));
    }

    private static Proposition sameAt(TermPath one, TermPath other) {
        return new Proposition.SameValue(new DecisionSubject.AnInput(one),
                new DecisionSubject.AnInput(other), true);
    }
}
