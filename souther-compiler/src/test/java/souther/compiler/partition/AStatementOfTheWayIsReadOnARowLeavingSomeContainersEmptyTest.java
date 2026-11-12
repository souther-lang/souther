package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.flow.Truth;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A statement of the way is read on a row holding some containers empty and the container the
 * relation stands inside holding one. What it comes to there is one of three: shown to hold, shown
 * to fail, or not worked out — and only the first lets a container be left empty, so a statement
 * the row fails is not one the row may be said to meet.
 */
class AStatementOfTheWayIsReadOnARowLeavingSomeContainersEmptyTest {

    private static final TermPath EMAILS = TermPath.of("emails");

    /** Stands in for how many {@code emails} holds: the reading asks the row for the number of a
     *  term and nothing else of it. */
    private static final NumericTerm HOW_MANY = new NumericTerm.ValueOf(EMAILS);

    /** The row holding one email. */
    private static final Function<NumericTerm, ExactRatio> ONE_HELD =
            term -> term.equals(HOW_MANY) ? ExactRatio.ONE : null;

    /** {@code HOW_MANY - n rel 0}. */
    private static UndividedByARelation.OnAWay howManyAgainst(long n, Rel rel) {
        return new UndividedByARelation.OnAWay(Set.of(EMAILS), true,
                new TakenConstraint.Affine(new LinearForm<>(ExactRatio.of(-n),
                        Map.of(HOW_MANY, ExactRatio.ONE)), rel),
                null, null, UndividedByARelation.OnAWay.PartsLeftAlone.NONE, null, null);
    }

    private static Truth onTheRow(UndividedByARelation.OnAWay condition,
                                  Function<NumericTerm, ExactRatio> held) {
        return UndividedByARelation.truthOnTheRow(condition, held, List.of());
    }

    @Test
    void holdingOneMeetsHoldingOneAtLeast() {
        assertEquals(Truth.TRUE, onTheRow(howManyAgainst(1, Rel.GE), ONE_HELD));
    }

    @Test
    void holdingOneFailsHoldingTwoAtLeast() {
        assertEquals(Truth.FALSE, onTheRow(howManyAgainst(2, Rel.GE), ONE_HELD));
    }

    @Test
    void holdingOneFailsHoldingNone() {
        assertEquals(Truth.FALSE, onTheRow(howManyAgainst(0, Rel.EQ), ONE_HELD));
    }

    @Test
    void aNumberTheRowDoesNotFixIsNotWorkedOut() {
        assertEquals(Truth.UNREAD, onTheRow(howManyAgainst(1, Rel.GE), term -> null));
    }
}
