package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a statement of one element is settled by the ways its forms of numbers stand and by what
 * the row holds at positions, which is what a reader that works those ways out needs: a part that
 * turns on other elements, as which of those holding a value is the last does, makes it false
 * wherever it stands in the statement.
 */
class AStatementIsOfFormsAndPositionsOnlyWhereNothingInItTurnsOnOtherElementsTest {

    private static Proposition above(long value) {
        return new Proposition.Compared(new Relation.Affine(new LinearForm<>(
                ExactRatio.of(-value), Map.of(new DecisionAtom.OfTheInput(
                        new NumericTerm.ValueOf(TermPath.of("month"))), ExactRatio.ONE)), Rel.GT),
                true);
    }

    private static Proposition truth(String at) {
        return new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of(at)), true);
    }

    private static Proposition lastOfItsKey() {
        return new Proposition.LastToHold(new DecisionSubject.AnInput(TermPath.of("xs")),
                new DecisionSubject.AnInput(TermPath.of("xs").then("key")), true);
    }

    @Test
    void aFormAndATruthOfAPositionAreSettledByThemselves() {
        assertTrue(AStatementAtARow.madeOfFormsAndPositions(above(3)));
        assertTrue(AStatementAtARow.madeOfFormsAndPositions(truth("active")));
        assertTrue(AStatementAtARow.madeOfFormsAndPositions(
                Proposition.all(List.of(above(3), truth("active")))));
        assertTrue(AStatementAtARow.madeOfFormsAndPositions(
                Proposition.any(List.of(above(3), above(5)))));
    }

    @Test
    void theLastOfTheElementsHoldingAValueTurnsOnTheOthersWhereverItStands() {
        assertFalse(AStatementAtARow.madeOfFormsAndPositions(lastOfItsKey()));
        assertFalse(AStatementAtARow.madeOfFormsAndPositions(
                Proposition.all(List.of(above(3), lastOfItsKey()))));
        assertFalse(AStatementAtARow.madeOfFormsAndPositions(
                Proposition.any(List.of(truth("active"), lastOfItsKey()))));
    }
}
