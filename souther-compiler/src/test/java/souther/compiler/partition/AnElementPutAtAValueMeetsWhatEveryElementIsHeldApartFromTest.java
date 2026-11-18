package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An element of a container put at a value meets what every element of it is held apart from
 * exactly where that value is, whatever the other places are, apart from it: the statement of
 * every element, with the value put in for the element, comes to a statement of no number that
 * holds. Anything less — a value it may be, or one that leaves a number to be asked of — is not
 * met by putting the element there.
 */
class AnElementPutAtAValueMeetsWhatEveryElementIsHeldApartFromTest {

    private static final TermPath HOLIDAYS = TermPath.of("holidays");

    private static final NumericTerm ELEMENT = new NumericTerm.ValueOf(HOLIDAYS.element());

    private static final NumericTerm FROM = new NumericTerm.ValueOf(TermPath.of("from"));

    private static final NumericTerm OTHER = new NumericTerm.ValueOf(TermPath.of("other"));

    /** {@code element - of - by}, held as {@code rel} against nought. */
    private static TakenConstraint.Affine moved(NumericTerm of, long by, Rel rel) {
        return new TakenConstraint.Affine(LinearForm.difference(ELEMENT, of)
                .minus(LinearForm.constant(ExactRatio.of(by))).orNull(), rel);
    }

    /** The element put at {@code of} moved by {@code by}, asked of {@code every}. */
    private static boolean meets(NumericTerm of, long by, TakenConstraint.Affine every) {
        return UndividedByARelation.meetsWhatEveryElementDoes(
                List.of(new RowDemand.Relational(moved(of, by, Rel.EQ))), HOLIDAYS, List.of(every));
    }

    @Test
    void anElementAtAnotherValueThanTheOneEveryElementIsKeptFromMeetsIt() {
        assertTrue(meets(FROM, 0, moved(FROM, 2, Rel.NE)));
        assertTrue(meets(FROM, 1, moved(FROM, 2, Rel.NE)));
    }

    @Test
    void anElementAtTheValueEveryElementIsKeptFromDoesNot() {
        assertFalse(meets(FROM, 2, moved(FROM, 2, Rel.NE)));
    }

    @Test
    void anElementAtAValueOfAnotherNumberLeavesThatNumberAskedOf() {
        assertFalse(meets(OTHER, 0, moved(FROM, 0, Rel.NE)));
    }
}
