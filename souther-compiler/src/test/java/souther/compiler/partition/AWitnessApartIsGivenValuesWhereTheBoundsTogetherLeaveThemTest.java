package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Values for the numbers a way asks apart from a relation are given where the statements together
 * leave them, and not where the region or any one statement does: under a region that says nothing,
 * {@code z + w >= 2}, {@code z + w <= 2}, {@code z - w >= 0} and {@code z - w <= 0} are met at one
 * each, and eliminating {@code z} to find that takes four pairs of bounds.
 */
class AWitnessApartIsGivenValuesWhereTheBoundsTogetherLeaveThemTest {

    private static final NumericTerm Z = new NumericTerm.ValueOf(TermPath.of("z"));

    private static final NumericTerm W = new NumericTerm.ValueOf(TermPath.of("w"));

    private static TakenConstraint.Affine stated(long constant, long z, long w, Rel rel) {
        return new TakenConstraint.Affine(new LinearForm<>(ExactRatio.of(constant),
                Map.of(Z, ExactRatio.of(z), W, ExactRatio.of(w))), rel);
    }

    private static final List<TakenConstraint.Affine> AT_ONE_EACH = List.of(
            stated(-2, 1, 1, Rel.GE), stated(-2, 1, 1, Rel.LE),
            stated(0, 1, -1, Rel.GE), stated(0, 1, -1, Rel.LE));

    private static WholeValuesMeeting.Witness sought(List<TakenConstraint.Affine> statements,
                                                     long pairs) {
        return WholeValuesMeeting.of(statements, NothingTheRulesSay.REGION,
                _ -> NumericDomain.Bounds.OPEN, pairs);
    }

    @Test
    void numbersBoundedTogetherAreGivenTheValuesTheBoundsTogetherLeave() {
        assertEquals(new WholeValuesMeeting.Witness.Found(
                Map.of(Z, ExactRatio.ONE, W, ExactRatio.ONE), 4), sought(AT_ONE_EACH, 4));
    }

    /** One pair short, {@code w} is given a value where nothing puts it, which leaves {@code z}
     *  none, and the figure is said to be why that may be. */
    @Test
    void anEliminationStoppedShortSaysSo() {
        assertEquals(new WholeValuesMeeting.Witness.NotShown(true, 0), sought(AT_ONE_EACH, 3));
    }

    private static final NumericTerm A = new NumericTerm.ValueOf(TermPath.of("a"));

    private static final NumericTerm B = new NumericTerm.ValueOf(TermPath.of("b"));

    /**
     * A bound the elimination finds that leaves the value taken where it was does not move it.
     * {@code 2b >= a + 101} and {@code 2b <= 2a + 201} leave {@code a} at minus a hundred or more,
     * which keeps nought, and nought leaves {@code b} fifty-one; minus a hundred would leave it
     * only a half.
     */
    @Test
    void aBoundThatKeepsTheValueTakenLeavesItTaken() {
        assertEquals(new WholeValuesMeeting.Witness.Found(
                Map.of(A, ExactRatio.ZERO, B, ExactRatio.of(51)), 1), sought(List.of(
                new TakenConstraint.Affine(new LinearForm<>(ExactRatio.of(-101),
                        Map.of(B, ExactRatio.of(2), A, ExactRatio.of(-1))), Rel.GE),
                new TakenConstraint.Affine(new LinearForm<>(ExactRatio.of(-201),
                        Map.of(B, ExactRatio.of(2), A, ExactRatio.of(-2))), Rel.LE)), 4));
    }

    /** {@code z + w} above nought and below one leaves rational values and no whole ones, which
     *  is no figure's doing. */
    @Test
    void boundsLeavingNoWholeValuesShowNoneAndNameNoFigure() {
        assertEquals(new WholeValuesMeeting.Witness.NotShown(false, 1), sought(List.of(
                stated(0, 1, 1, Rel.GT), stated(-1, 1, 1, Rel.LT)), 4));
    }
}
