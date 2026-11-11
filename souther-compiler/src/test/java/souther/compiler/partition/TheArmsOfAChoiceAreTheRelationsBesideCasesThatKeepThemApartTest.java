package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.Case;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * The cases an arm is chosen by are taken away from it only where the statement is the arms of one
 * choice: the cases of one subject, no two of which share a case. A disjunction of two relations
 * each beside conditions of its own says nothing of an arm, and is read as the one statement it
 * is.
 */
class TheArmsOfAChoiceAreTheRelationsBesideCasesThatKeepThemApartTest {

    private static final TermPath CHOSEN = TermPath.of("chosen");
    private static final TermPath MONTH = TermPath.of("month");

    @Test
    void armsWhoseCasesShareNoneAreEachTheRelationBesideThem() {
        Proposition stated = Proposition.any(List.of(
                Proposition.all(List.of(inCases(CHOSEN, "A"), above(12))),
                Proposition.all(List.of(inCases(CHOSEN, "B", "C"), above(24)))));
        assertEquals(List.of(above(12), above(24)), Cutting.armsOfAChoice(stated));
    }

    @Test
    void armsThatMayBothHoldAreNotTheArmsOfAChoice() {
        Proposition stated = Proposition.any(List.of(
                Proposition.all(List.of(inCases(CHOSEN, "A", "B"), above(12))),
                Proposition.all(List.of(inCases(CHOSEN, "B", "C"), above(24)))));
        assertNull(Cutting.armsOfAChoice(stated));
    }

    @Test
    void armsChosenOnTwoSubjectsAreNotTheArmsOfOneChoice() {
        Proposition stated = Proposition.any(List.of(
                Proposition.all(List.of(inCases(CHOSEN, "A"), above(12))),
                Proposition.all(List.of(inCases(TermPath.of("other"), "B"), above(24)))));
        assertNull(Cutting.armsOfAChoice(stated));
    }

    /** What a model writes with a flag instead of a match is no choice by cases: nothing of it is
     *  taken away, whatever it comes to. */
    @Test
    void aFlagWrittenInPlaceOfCasesIsNoChoiceByCases() {
        Proposition flag = new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of("flag")),
                true);
        Proposition stated = Proposition.any(List.of(
                Proposition.all(List.of(flag, above(12))),
                Proposition.all(List.of(flag.denied(), above(24)))));
        assertNull(Cutting.armsOfAChoice(stated));
    }

    @Test
    void anArmStatingMoreThanOneRelationIsNotReadAsOne() {
        Proposition stated = Proposition.any(List.of(
                Proposition.all(List.of(inCases(CHOSEN, "A"), above(12), above(13))),
                Proposition.all(List.of(inCases(CHOSEN, "B"), above(24)))));
        assertNull(Cutting.armsOfAChoice(stated));
    }

    /** The month above {@code value}, held. */
    private static Proposition.Compared above(long value) {
        return new Proposition.Compared(new Relation.Affine(new LinearForm<>(
                ExactRatio.of(-value), Map.of(new DecisionAtom.OfTheInput(
                        new NumericTerm.ValueOf(MONTH)), ExactRatio.ONE)), Rel.GT), true);
    }

    /** {@code at} being one of {@code leaves}. */
    private static Proposition inCases(TermPath at, String... leaves) {
        List<Refinement> atoms = new ArrayList<>();
        for (String leaf : leaves) {
            TypeSymbol symbol = TypeSymbols.declared(new TypeKey("probe", leaf));
            atoms.add(Refinement.of(new Case.SumCase(symbol, true)));
        }
        return new Proposition.InCases(new DecisionSubject.AnInput(at), CasesLeft.ofEach(atoms),
                true);
    }
}
