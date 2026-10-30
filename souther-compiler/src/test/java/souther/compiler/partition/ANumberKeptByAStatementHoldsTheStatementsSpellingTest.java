package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.ElementKey;
import souther.compiler.inputs.ElementProjection;
import souther.compiler.inputs.ElementValue;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Spelling;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.types.Type;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A number of the occurrences a statement keeps is spelled with the statement's own spelling held
 * inside it, and so is everything spelled out of that number: a product it is a factor of, the
 * input's number it is in a relation, and a count of the elements meeting the statement. Written
 * out, the statement's text would be copied into each of them.
 */
class ANumberKeptByAStatementHoldsTheStatementsSpellingTest {

    private static final TermPath LINES = TermPath.of("orders").element().then("lines");
    private static final TermPath LINE = LINES.element();
    private static final TermPath QTY = LINE.then("qty");
    private static final TermPath LIMIT = TermPath.of("limit");

    private static final Proposition HAS_A_QUANTITY =
            new Proposition.Present(new DecisionSubject.AnInput(QTY), true);

    private static final KeptOccurrences KEPT = new KeptOccurrences(
            new DecisionSubject.AnInput(LINES), HAS_A_QUANTITY,
            AStatementAtARow.of(HAS_A_QUANTITY, "f", null));

    private static final NumericTerm COUNTED = NumericTerm.OccurrencesOfItsValue.of(
            new RunSource.FlattenedOccurrences(LINE), KEPT);

    private static final NumericTerm GATHERED = NumericTerm.GatheredUnderItsKey.of(LINE,
            new ElementKey.At(ElementProjection.ofFields(List.of("sku"))),
            new ElementValue.Affine(LinearForm.atom(ElementProjection.ofFields(List.of("qty")))),
            Type.Prim.INT, NumericTerm.GatheredUnderItsKey.Gathering.TOTAL, KEPT);

    @Test
    void everyNumberSpelledOutOfAKeptOneHoldsTheStatementsSpelling() {
        Spelling statement = HAS_A_QUANTITY.spelling();
        NumericTerm product = NumericTerm.ProductOf.of(
                new LinearForm<>(ExactRatio.ONE, Map.of(GATHERED, ExactRatio.of(2))),
                LinearForm.atom(new NumericTerm.ValueOf(LIMIT)));
        for (NumericTerm kept : List.of(COUNTED, GATHERED, product)) {
            assertTrue(kept.spelling().holdsWithin(statement), kept::toString);
            assertTrue(new DecisionAtom.OfTheInput(kept).spelling().holdsWithin(statement),
                    kept::toString);
        }
        assertTrue(KEPT.spelling().holdsWithin(statement), KEPT::key);
    }
}
