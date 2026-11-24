package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * That a way holds a row is shown by numbers that meet each of its statements, and not by what a
 * region leaves a form: no decimal makes {@code 3 * (d - h)} one, though nothing about the range
 * of {@code d - h} says so.
 */
class AWitnessOfDifferencesTest {

    private static final NumericTerm D = new NumericTerm.ValueOf(TermPath.of("d"));
    private static final NumericTerm H = new NumericTerm.ValueOf(TermPath.of("h"));
    private static final NumericTerm S = new NumericTerm.ValueOf(TermPath.of("s"));

    /** {@code weight * (one - other) + constant}, held against nought as {@code rel}. */
    private static TakenConstraint.Affine of(Rel rel, long weight, long constant,
                                             NumericTerm one, NumericTerm other) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(one, ExactRatio.of(weight));
        coefs.put(other, ExactRatio.of(-weight));
        return new TakenConstraint.Affine(new LinearForm<>(ExactRatio.of(constant), coefs), rel);
    }

    @Test
    void aWayWhoseNumbersMakeEachStatementHoldsARow() {
        // d > h, d /= s, h - s + 1 >= 0
        assertTrue(AWitnessOfDifferences.exists(List.of(of(Rel.GT, 1, 0, D, H),
                of(Rel.NE, 1, 0, D, S), of(Rel.GE, 1, 1, H, S))));
    }

    /** {@code 3 * (d - h) == 1} needs a difference of a third, which is no step of the grid and
     *  no finite decimal either. */
    @Test
    void aWayNoFiniteDecimalMeetsHoldsNoRowShown() {
        assertFalse(AWitnessOfDifferences.exists(List.of(of(Rel.EQ, 3, -1, D, H))));
    }

    @Test
    void aWayTheSameShapeMeetsAtAHalfHoldsOne() {
        assertTrue(AWitnessOfDifferences.exists(List.of(of(Rel.EQ, 2, -1, D, H))));
    }

    @Test
    void statementsNoNumbersMeetTogetherHoldNoRow() {
        assertFalse(AWitnessOfDifferences.exists(
                List.of(of(Rel.GT, 1, 0, D, H), of(Rel.LT, 1, 0, D, H))));
        assertFalse(AWitnessOfDifferences.exists(
                List.of(of(Rel.EQ, 1, 0, D, H), of(Rel.NE, 1, 0, D, H))));
    }

    @Test
    void aWayOfNoStatementIsNoRowShownEither() {
        assertFalse(AWitnessOfDifferences.exists(List.of()));
    }
}
