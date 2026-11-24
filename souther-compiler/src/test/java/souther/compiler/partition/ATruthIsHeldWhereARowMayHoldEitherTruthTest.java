package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.partition.UndividedByARelation.OnAWay;

import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.function.Predicate;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A set of places read only by truths is held where some row holds each truth asked at its place
 * and the way holds each place to one of them. Held to both, or to a truth no row holds there, it
 * is not.
 */
class ATruthIsHeldWhereARowMayHoldEitherTruthTest {

    private static final TermPath SIDE = TermPath.of("s");
    private static final TermPath FLAG = TermPath.of("f");

    private static OnAWay holding(boolean truth) {
        return new OnAWay(Set.of(FLAG), false, null, null, null, OnAWay.PartsLeftAlone.NONE, null,
                null, null, null, new RowDemand.ATruth(FLAG, truth));
    }

    private static Optional<Set<TermPath>> heldApart(List<OnAWay> truths,
                                                     Predicate<RowDemand.ATruth> aRowHolds) {
        return PlacesTiedAlongAWay.of(truths, List.of(), List.of(SIDE), _ -> null, aRowHolds)
                .heldApartFrom(new NumericTerm.ValueOf(SIDE), FLAG);
    }

    @Test
    void aTruthSomeRowHoldsIsHeld() {
        assertEquals(Optional.of(Set.of(FLAG)), heldApart(List.of(holding(true)), _ -> true));
    }

    @Test
    void bothTruthsAtOnePlaceAreNotHeld() {
        assertEquals(Optional.empty(),
                heldApart(List.of(holding(true), holding(false)), _ -> true));
    }

    @Test
    void aTruthNoRowIsShownToHoldIsNotHeld() {
        assertEquals(Optional.empty(), heldApart(List.of(holding(true)), _ -> false));
    }
}
