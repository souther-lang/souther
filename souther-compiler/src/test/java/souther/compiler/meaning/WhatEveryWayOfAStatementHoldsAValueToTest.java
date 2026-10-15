package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.Case;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a statement holds a value of the input to is what every way of it does, read through the
 * whole of it and not off its outermost parts.
 *
 * <p>Where a line decides can be said as one of many things — the cases past the number said one
 * by one, read whole — and each of them still asks the term to be the first: the line decides
 * only there, and a reader is owed that whatever else the ways tell apart.
 */
class WhatEveryWayOfAStatementHoldsAValueToTest {

    private static final TermPath TERM = TermPath.of("term");

    @Test
    void aCaseEveryWayAsksIsHeld() {
        Proposition stated = Proposition.any(List.of(
                Proposition.all(List.of(inCases("OneYear"), truth("q", true))),
                Proposition.all(List.of(inCases("OneYear"), truth("q", false), truth("r", true))),
                Proposition.all(List.of(inCases("OneYear"), above(3)))));
        assertEquals(Map.of(TERM, new CasesHeldTo.Held.OneOf(cases("OneYear"))),
                CasesHeldTo.of(stated));
    }

    @Test
    void waysAskingTwoCasesHoldTheValueToEither() {
        Proposition stated = Proposition.any(List.of(
                Proposition.all(List.of(inCases("OneYear"), truth("q", true))),
                Proposition.all(List.of(inCases("TwoYear"), truth("q", true)))));
        assertEquals(Map.of(TERM, new CasesHeldTo.Held.OneOf(cases("OneYear", "TwoYear")),
                        TermPath.of("q"), new CasesHeldTo.Held.ATruth(true)),
                CasesHeldTo.of(stated));
    }

    @Test
    void aWayAskingNothingOfAValueHoldsItToNothing() {
        Proposition stated = Proposition.any(List.of(
                Proposition.all(List.of(inCases("OneYear"), truth("q", true))),
                above(3)));
        assertEquals(Map.of(), CasesHeldTo.of(stated));
    }

    @Test
    void casesAValueIsHeldOutOfAreLeftOutOfTheCasesItIsHeldTo() {
        Proposition stated = Proposition.all(List.of(inCases("A", "B", "C"),
                inCases("B").denied()));
        assertEquals(Map.of(TERM, new CasesHeldTo.Held.OneOf(cases("A", "C"))),
                CasesHeldTo.of(stated));
    }

    private static Proposition inCases(String... leaves) {
        return new Proposition.InCases(new DecisionSubject.AnInput(TERM), cases(leaves), true);
    }

    private static CasesLeft cases(String... leaves) {
        List<Refinement> atoms = new ArrayList<>();
        for (String leaf : leaves) {
            atoms.add(Refinement.of(new Case.SumCase(
                    TypeSymbols.declared(new TypeKey("probe", leaf)), true)));
        }
        return CasesLeft.ofEach(atoms);
    }

    private static Proposition truth(String at, boolean holds) {
        return new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of(at)), holds);
    }

    private static Proposition above(long value) {
        return new Proposition.Compared(new Relation.Affine(new LinearForm<>(
                ExactRatio.of(-value), Map.of(new DecisionAtom.OfTheInput(
                        new NumericTerm.ValueOf(TermPath.of("month"))), ExactRatio.ONE)), Rel.GT),
                true);
    }
}
