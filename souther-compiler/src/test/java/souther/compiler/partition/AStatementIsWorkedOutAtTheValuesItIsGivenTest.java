package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value shown to meet what a way asks apart from a relation is a value the statements are worked
 * out at, and not where the region puts the numbers: a region answers where values lie, which may
 * be wider than the statements leave them.
 */
class AStatementIsWorkedOutAtTheValuesItIsGivenTest {

    private static final NumericTerm REVENUE = new NumericTerm.ValueOf(TermPath.of("revenue"));

    private static final NumericTerm INSURED = new NumericTerm.ValueOf(TermPath.of("insured"));

    /** {@code revenue * 2 < insured}, as the form {@code 2 revenue - insured} below nought. */
    private static final TakenConstraint.Affine UNDER_HALF = new TakenConstraint.Affine(
            new LinearForm<>(ExactRatio.ZERO, Map.of(REVENUE, ExactRatio.of(2),
                    INSURED, ExactRatio.of(-1))), Rel.LT);

    @Test
    void aStatementHoldsWhereItsNumbersStandAsItAsks() {
        assertTrue(UndividedByARelation.holdsAt(UNDER_HALF,
                Map.of(REVENUE, ExactRatio.ZERO, INSURED, ExactRatio.ONE)));
    }

    /** Both at nought are each where a region of the two at nought or above puts them, and
     *  together not a row the statement lets through. */
    @Test
    void valuesEachWhereTheirRunPutsThemNeedNotMeetTheStatementTogether() {
        assertFalse(UndividedByARelation.holdsAt(UNDER_HALF,
                Map.of(REVENUE, ExactRatio.ZERO, INSURED, ExactRatio.ZERO)));
    }

    @Test
    void aStatementOfANumberGivenNoValueIsNotShownToHold() {
        assertFalse(UndividedByARelation.holdsAt(UNDER_HALF, Map.of(REVENUE, ExactRatio.ZERO)));
    }
}
