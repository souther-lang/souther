package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Rel;
import souther.compiler.partition.CompositionBudget;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static souther.compiler.meaning.TheInputsACaseHoldsFor.X;
import static souther.compiler.meaning.TheInputsACaseHoldsFor.Y;
import static souther.compiler.meaning.TheInputsACaseHoldsFor.relation;
import static souther.compiler.meaning.TheInputsACaseHoldsFor.remainder;
import static souther.compiler.meaning.TheInputsACaseHoldsFor.someCaseCrosses;

/**
 * Where a line at a remainder is proved to decide in none of the cases it is said for, no two
 * inputs, one holding the line and one failing it, meet the same case.
 *
 * <p>Each case below carries one rule of the proof: what a condition holds at, its denial and its
 * offset, how an {@code All} and an {@code Any} of conditions hold, what a choice leaves open and
 * what a case held together fixes, and what is not read. The inputs are the numbers a remainder by
 * three tells apart twice over, tried whole by a count worked out here and not by the proof.
 */
class NoCaseCrossesProvesNoneWhereAPairOfRowsMeetsOneCaseTest {

    /** The numbers a remainder by three tells apart twice over. */
    private static List<TheInputsACaseHoldsFor.Input> everyInput() {
        return TheInputsACaseHoldsFor.inputs(0, 5, false);
    }

    private static boolean proves(Proposition.Compared line, DecidingCase.Cases cases) {
        return NoCaseCrosses.proves(line, new DecidingCase(line, cases), _ -> true);
    }

    private static Proposition.Compared remainderLine(int offset, int least) {
        return relation(Map.of(remainder(X, offset, 3), 1), -least, Rel.GE, true);
    }

    @Test
    void casesThatFixTheRemainderToOneSideOfTheLineAreProvedToHaveNoRowOnEachSide() {
        Proposition.Compared line = remainderLine(0, 1);
        DecidingCase.Cases cases = DecidingCase.Cases.together(List.of(
                new DecidingCase.Cases.One(relation(Map.of(remainder(X, 1, 3), 1), 0, Rel.EQ, true)),
                new DecidingCase.Cases.One(relation(Map.of(Y, 1), -2, Rel.GE, true))));

        assertFalse(someCaseCrosses(line, cases, everyInput()), "x + 1 is 0 mod 3, so x is 2");
        assertTrue(proves(line, cases));
    }

    @Test
    void casesThatLeaveBothSidesOfTheLineAreNotProved() {
        Proposition.Compared line = remainderLine(0, 1);
        DecidingCase.Cases cases = new DecidingCase.Cases.One(
                relation(Map.of(Y, 1), -2, Rel.GE, true));

        assertTrue(someCaseCrosses(line, cases, everyInput()));
        assertFalse(proves(line, cases));
    }

    @Test
    void whatOneAlternativeLeavesOpenIsLeftOpenByTheCasesThatChooseIt() {
        Proposition.Compared line = remainderLine(0, 1);
        DecidingCase.Cases fixed = new DecidingCase.Cases.One(
                relation(Map.of(remainder(X, 0, 3), 1), 0, Rel.EQ, true));
        DecidingCase.Cases open = new DecidingCase.Cases.One(
                relation(Map.of(Y, 1), -2, Rel.GE, true));
        DecidingCase.Cases cases = new DecidingCase.Cases.EachOf(List.of(fixed, open));

        assertTrue(someCaseCrosses(line, cases, everyInput()), "the second alternative");
        assertFalse(proves(line, cases));
    }

    @Test
    void aFactorThatFixesTheRemainderFixesItForTheWholeCase() {
        Proposition.Compared line = remainderLine(0, 1);
        DecidingCase.Cases fixed = new DecidingCase.Cases.One(
                relation(Map.of(remainder(X, 0, 3), 1), 0, Rel.EQ, true));
        DecidingCase.Cases open = new DecidingCase.Cases.EachOf(List.of(
                new DecidingCase.Cases.One(relation(Map.of(Y, 1), -2, Rel.GE, true)),
                new DecidingCase.Cases.One(relation(Map.of(Y, 1), -2, Rel.GE, false))));
        DecidingCase.Cases cases = DecidingCase.Cases.together(List.of(fixed, open));

        assertFalse(someCaseCrosses(line, cases, everyInput()));
        assertTrue(proves(line, cases));
    }

    @Test
    void casesNobodyTookApartAreNotProved() {
        Proposition.Compared line = remainderLine(0, 1);
        DecidingCase.Cases cases = new DecidingCase.Cases.NotTakenApart(
                CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.atDeclared());

        assertTrue(someCaseCrosses(line, cases, everyInput()), "any two rows are of them");
        assertFalse(proves(line, cases));
    }

    @Test
    void theOffsetOfARemainderMovesTheResiduesItHoldsAt() {
        // (x + 1) mod 3 is at least 1 for x of 0 and 1, and the line holds at 0 alone: x of 0
        // and x of 1 are two rows of one case, one each side.
        Proposition.Compared line = relation(Map.of(remainder(X, 0, 3), 1), 0, Rel.EQ, true);
        DecidingCase.Cases cases = new DecidingCase.Cases.One(
                relation(Map.of(remainder(X, 1, 3), 1), -1, Rel.GE, true));

        assertTrue(someCaseCrosses(line, cases, everyInput()));
        assertFalse(proves(line, cases));
    }

    @Test
    void aConditionDeniedHoldsAtTheResiduesItsRelationDoesNot() {
        // Not (x mod 3 >= 1) is x of 0 mod 3, where the line x mod 3 >= 1 holds at no row.
        Proposition.Compared line = remainderLine(0, 1);
        DecidingCase.Cases cases = new DecidingCase.Cases.One(
                relation(Map.of(remainder(X, 0, 3), 1), -1, Rel.GE, false));

        assertFalse(someCaseCrosses(line, cases, everyInput()));
        assertTrue(proves(line, cases));
    }

    @Test
    void everyPartOfAConjunctionHoldsAndSomePartOfADisjunctionDoes() {
        Proposition.Compared line = remainderLine(0, 1);
        Proposition one = relation(Map.of(remainder(X, 0, 3), 1), -1, Rel.GE, true);
        Proposition two = relation(Map.of(remainder(X, 0, 3), 1), -2, Rel.GE, false);
        DecidingCase.Cases both = new DecidingCase.Cases.One(Proposition.all(List.of(one, two)));
        DecidingCase.Cases either = new DecidingCase.Cases.One(Proposition.any(List.of(one, two)));

        assertFalse(someCaseCrosses(line, both, everyInput()), "x mod 3 is 1 and no more");
        assertTrue(proves(line, both));
        assertTrue(someCaseCrosses(line, either, everyInput()), "x mod 3 is below 2 or at least 1, which is any");
        assertFalse(proves(line, either));
    }
}
