package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.partition.UndividedByARelation.OnAWay;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A disequality takes one hyperplane out of a run with both sides open, so it ties no side of a
 * relation to another — unless it is the line the relation is drawn at, which the equalities of the
 * way decide: {@code h /= s} beside {@code d == h} keeps {@code d} off {@code s}, and a relation
 * between {@code d} and {@code s} is drawn at that line. Judged by the form as it was written,
 * the one is another line and the other is the same.
 */
class ADisequalityTiesTheSidesOnlyWhereItIsTheLineOfTheRelationOnceTheEqualitiesAreInTest {

    private static final NumericTerm D = new NumericTerm.ValueOf(TermPath.of("d"));
    private static final NumericTerm H = new NumericTerm.ValueOf(TermPath.of("h"));
    private static final NumericTerm K = new NumericTerm.ValueOf(TermPath.of("k"));
    private static final NumericTerm S = new NumericTerm.ValueOf(TermPath.of("s"));

    private static TakenConstraint.Affine affine(NumericTerm one, NumericTerm other, Rel rel) {
        return new TakenConstraint.Affine(LinearForm.<NumericTerm>difference(one, other), rel);
    }

    private static OnAWay equality(NumericTerm one, NumericTerm other) {
        return new OnAWay(Set.of(TermPath.of("x")), false, affine(one, other, Rel.EQ), null, null,
                OnAWay.PartsLeftAlone.NONE, null, null);
    }

    /** {@code d - s} held against nought: the relation {@code d >= s} drawn at its line. */
    private static TakenConstraint.Affine lineOfDAndS() {
        return affine(D, S, Rel.GE);
    }

    @Test
    void aDisequalityOfTheNumbersTheEqualityDefinesIsTheLineOnceTheyAreIn() {
        TakenConstraint.Affine kept = affine(H, S, Rel.NE);

        assertTrue(UndividedByARelation.keepsTheLine(kept, lineOfDAndS(),
                UndividedByARelation.stepsOf(List.of(equality(D, H)))));
    }

    @Test
    void theSameDisequalityIsAnotherLineBesideNoEquality() {
        TakenConstraint.Affine kept = affine(H, S, Rel.NE);

        assertFalse(UndividedByARelation.keepsTheLine(kept, lineOfDAndS(),
                UndividedByARelation.stepsOf(List.of())));
    }

    @Test
    void equalitiesInAChainDefineTheNumbersOneAfterTheOther() {
        TakenConstraint.Affine kept = affine(K, S, Rel.NE);

        assertTrue(UndividedByARelation.keepsTheLine(kept, lineOfDAndS(),
                UndividedByARelation.stepsOf(List.of(equality(D, H), equality(H, K)))));
        assertFalse(UndividedByARelation.keepsTheLine(kept, lineOfDAndS(),
                UndividedByARelation.stepsOf(List.of(equality(D, H)))));
    }

    /** {@code d - s + 1 /= 0} is the line {@code d - s = -1}, which {@code d >= s} is not drawn at. */
    @Test
    void aDisequalityBesideTheLineButNotOnItTiesNothingWhateverTheEqualities() {
        TakenConstraint.Affine kept = new TakenConstraint.Affine(new LinearForm<>(ExactRatio.ONE,
                LinearForm.<NumericTerm>difference(D, S).coefs()), Rel.NE);

        assertFalse(UndividedByARelation.keepsTheLine(kept, lineOfDAndS(),
                UndividedByARelation.stepsOf(List.of())));
        assertFalse(UndividedByARelation.keepsTheLine(kept, lineOfDAndS(),
                UndividedByARelation.stepsOf(List.of(equality(H, K)))));
    }

    /** A disequality that holds whatever the others are, once they are in, ties nothing. */
    @Test
    void aDisequalityThatHoldsWhateverTheOthersAreTiesNothing() {
        TakenConstraint.Affine kept = new TakenConstraint.Affine(new LinearForm<>(ExactRatio.ONE,
                LinearForm.<NumericTerm>difference(D, H).coefs()), Rel.NE);

        assertFalse(UndividedByARelation.keepsTheLine(kept, lineOfDAndS(),
                UndividedByARelation.stepsOf(List.of(equality(D, H)))));
    }
}
