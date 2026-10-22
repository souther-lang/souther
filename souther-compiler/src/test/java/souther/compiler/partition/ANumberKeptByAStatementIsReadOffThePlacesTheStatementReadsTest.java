package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.ElementKey;
import souther.compiler.inputs.ElementProjection;
import souther.compiler.inputs.ElementValue;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.numeric.LinearForm;
import souther.compiler.types.Type;

import java.util.List;
import java.util.function.UnaryOperator;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A number of the occurrences a statement keeps is read off the places the statement reads as
 * well as off its own, and moves only with all of them where they stand.
 *
 * <p>The statement names places of the input it was read in, and nothing moves a statement. So
 * the number is the same number under a move that leaves every one of those places where it is —
 * the move that asks where it is read off among them — and no number under one that does not.
 * Read as moving nowhere, it would answer that it is read off nothing, and a number apart from
 * every other is one nothing it reads can stand beside.
 */
class ANumberKeptByAStatementIsReadOffThePlacesTheStatementReadsTest {

    private static final TermPath LINES = TermPath.of("orders").element().then("lines");
    private static final TermPath LINE = LINES.element();
    private static final TermPath QTY = LINE.then("qty");

    /** The lines that hold some quantity. */
    private static final Proposition HAS_A_QUANTITY =
            new Proposition.Present(new DecisionSubject.AnInput(QTY), true);

    private static final KeptOccurrences KEPT = new KeptOccurrences(
            new DecisionSubject.AnInput(LINES), HAS_A_QUANTITY,
            AStatementAtARow.of(HAS_A_QUANTITY, "f", null));

    /** How often each line's value occurs among the lines kept. */
    private static final NumericTerm COUNTED = NumericTerm.OccurrencesOfItsValue.of(
            new RunSource.FlattenedOccurrences(LINE), KEPT);

    /** The total of each sku's quantities among the lines kept. */
    private static final NumericTerm GATHERED = NumericTerm.GatheredUnderItsKey.of(LINE,
            new ElementKey.At(ElementProjection.ofFields(List.of("sku"))),
            new ElementValue.Affine(LinearForm.atom(ElementProjection.ofFields(List.of("qty")))),
            Type.Prim.INT, NumericTerm.GatheredUnderItsKey.Gathering.TOTAL, KEPT);

    @Test
    void aKeptNumberIsReadOffItsOwnPlacesAndTheStatementsToo() {
        for (NumericTerm kept : List.of(COUNTED, GATHERED)) {
            List<TermPath> places = kept.placesReadOff();
            assertTrue(places.contains(QTY) && places.contains(LINES),
                    () -> kept + " is read off " + places);
            assertTrue(kept.sharesAPlaceWith(new NumericTerm.ValueOf(QTY)), kept::toString);
        }
    }

    @Test
    void aKeptNumberMovedWhereItStandsIsTheSameNumber() {
        for (NumericTerm kept : List.of(COUNTED, GATHERED)) {
            assertEquals(kept, kept.movedTo(UnaryOperator.identity()), kept::toString);
        }
    }

    /**
     * A move that takes a place the statement reads somewhere else leaves the statement naming
     * places of another input, which is no number of that one — though the run itself moves to
     * a run of the same shape, as the same number without the statement does.
     */
    @Test
    void aKeptNumberMovedOffThePlacesItsStatementReadsIsNoNumber() {
        UnaryOperator<TermPath> moved = at -> at.head().equals("orders")
                ? new TermPath("other", at.steps()) : at;
        for (NumericTerm kept : List.of(COUNTED, GATHERED)) {
            assertNull(kept.movedTo(moved), kept::toString);
        }
        assertNotNull(NumericTerm.OccurrencesOfItsValue.of(new RunSource.FlattenedOccurrences(LINE))
                .movedTo(moved), "the run moves");
    }
}
