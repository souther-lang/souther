package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.partition.UndividedByARelation.OnAWay;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
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

    /** {@code constant} and each term weighed, held against nought as {@code rel}. */
    private static TakenConstraint.Affine weighed(Rel rel, long constant,
                                                  Object... termsAndWeights) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        for (int i = 0; i < termsAndWeights.length; i += 2) {
            coefs.put((NumericTerm) termsAndWeights[i],
                    ExactRatio.of(((Number) termsAndWeights[i + 1]).longValue()));
        }
        return new TakenConstraint.Affine(new LinearForm<>(ExactRatio.of(constant), coefs), rel);
    }

    private static List<UndividedByARelation.Step> stepsOf(TakenConstraint.Affine... equalities) {
        return UndividedByARelation.stepsOf(List.of(equalities));
    }

    /** {@code d - s} held against nought: the relation {@code d >= s} drawn at its line. */
    private static TakenConstraint.Affine lineOfDAndS() {
        return affine(D, S, Rel.GE);
    }

    @Test
    void aDisequalityOfTheNumbersTheEqualityDefinesIsTheLineOnceTheyAreIn() {
        TakenConstraint.Affine kept = affine(H, S, Rel.NE);

        assertTrue(UndividedByARelation.keepsTheLine(kept, lineOfDAndS(),
                stepsOf(affine(D, H, Rel.EQ))));
    }

    @Test
    void theSameDisequalityIsAnotherLineBesideNoEquality() {
        TakenConstraint.Affine kept = affine(H, S, Rel.NE);

        assertFalse(UndividedByARelation.keepsTheLine(kept, lineOfDAndS(), stepsOf()));
    }

    @Test
    void equalitiesInAChainDefineTheNumbersOneAfterTheOther() {
        TakenConstraint.Affine kept = affine(K, S, Rel.NE);

        assertTrue(UndividedByARelation.keepsTheLine(kept, lineOfDAndS(),
                stepsOf(affine(D, H, Rel.EQ), affine(H, K, Rel.EQ))));
        assertFalse(UndividedByARelation.keepsTheLine(kept, lineOfDAndS(),
                stepsOf(affine(D, H, Rel.EQ))));
    }

    /** {@code d - s + 1 /= 0} is the line {@code d - s = -1}, which {@code d >= s} is not drawn at. */
    @Test
    void aDisequalityBesideTheLineButNotOnItTiesNothingWhateverTheEqualities() {
        TakenConstraint.Affine kept = weighed(Rel.NE, 1, D, 1, S, -1);

        assertFalse(UndividedByARelation.keepsTheLine(kept, lineOfDAndS(), stepsOf()));
        assertFalse(UndividedByARelation.keepsTheLine(kept, lineOfDAndS(),
                stepsOf(affine(H, K, Rel.EQ))));
    }

    /** A disequality that holds whatever the others are, once they are in, ties nothing. */
    @Test
    void aDisequalityThatHoldsWhateverTheOthersAreTiesNothing() {
        TakenConstraint.Affine kept = weighed(Rel.NE, 1, D, 1, H, -1);

        assertFalse(UndividedByARelation.keepsTheLine(kept, lineOfDAndS(),
                stepsOf(affine(D, H, Rel.EQ))));
    }

    /**
     * A number put in the terms of the others keeps each weight and the constant: {@code d = 2h +
     * 3} put in {@code d - s + 1 >= 0} is {@code 2h - s + 4 >= 0}, and a number weighed otherwise
     * than once is put in as the quotient it is, so that {@code 2d = h} put in
     * {@code 2d - s >= 0} is {@code h - s >= 0}.
     */
    @Test
    void aNumberPutInTheTermsOfTheOthersKeepsEveryWeightAndTheConstant() {
        var definedAsTwiceHPlusThree = stepsOf(weighed(Rel.EQ, -3, D, 1, H, -2));
        assertEquals(List.of(weighed(Rel.GE, 4, H, 2, S, -1)), UndividedByARelation.reducedBy(
                weighed(Rel.GE, 1, D, 1, S, -1), definedAsTwiceHPlusThree));

        var twiceDIsH = stepsOf(weighed(Rel.EQ, 0, D, 2, H, -1));
        assertEquals(List.of(weighed(Rel.GE, 0, H, 1, S, -1)), UndividedByARelation.reducedBy(
                weighed(Rel.GE, 0, D, 2, S, -1), twiceDIsH));
    }

    private static NumericDomain.FormProjection projection(Endpoint least, Endpoint greatest) {
        return new NumericDomain.FormProjection.Within(new NumericDomain.Bounds(least, greatest));
    }

    /** Where the region leaves the difference of two numbers one value, that is an equality of
     *  the way ({@code h >= s} and {@code h <= s} leave {@code h - s} nought). */
    @Test
    void aDifferenceTheRegionLeavesOneValueIsAnEquality() {
        assertEquals(List.of(affine(H, S, Rel.EQ)), UndividedByARelation.equalitiesHeldBy(
                _ -> projection(Endpoint.inclusive(Count.of(0)), Endpoint.inclusive(Count.of(0))),
                List.of(H, S)));
        assertEquals(List.of(weighed(Rel.EQ, -2, H, 1, S, -1)),
                UndividedByARelation.equalitiesHeldBy(_ -> projection(
                        Endpoint.inclusive(Count.of(2)), Endpoint.inclusive(Count.of(2))),
                        List.of(H, S)));
    }

    /** A difference left a run is no equality, nor one that has an end open, nor one the
     *  region leaves nothing: {@code h >= 0} and {@code h <= s} leave {@code h - s} the values
     *  below nought, and nought only where {@code s} is nought. */
    @Test
    void aDifferenceTheRegionLeavesARunOrNothingIsNoEquality() {
        assertEquals(List.of(), UndividedByARelation.equalitiesHeldBy(
                _ -> projection(null, Endpoint.inclusive(Count.of(0))), List.of(H, S)));
        assertEquals(List.of(), UndividedByARelation.equalitiesHeldBy(
                _ -> projection(Endpoint.inclusive(Count.of(0)), Endpoint.exclusive(Count.of(0))),
                List.of(H, S)));
        assertEquals(List.of(), UndividedByARelation.equalitiesHeldBy(
                _ -> new NumericDomain.FormProjection.NothingIsLeft(), List.of(H, S)));
    }

    /** What the way states of numbers by an equality is taken; a disequality, or a statement of
     *  which case a value is, is not. */
    @Test
    void theEqualitiesAWayStatesAreThoseOfNumbers() {
        Set<TermPath> at = Set.of(TermPath.of("x"));
        OnAWay equality = new OnAWay(at, false, affine(D, H, Rel.EQ), null, null,
                OnAWay.PartsLeftAlone.NONE, null, null);
        OnAWay disequality = new OnAWay(at, false, affine(D, H, Rel.NE), null, null,
                OnAWay.PartsLeftAlone.NONE, null, null);
        OnAWay whichCase = new OnAWay(at, true, affine(D, H, Rel.EQ), null, null,
                OnAWay.PartsLeftAlone.NONE, null, null);

        assertEquals(List.of(affine(D, H, Rel.EQ)),
                UndividedByARelation.equalitiesOf(List.of(equality, disequality, whichCase)));
    }
}
