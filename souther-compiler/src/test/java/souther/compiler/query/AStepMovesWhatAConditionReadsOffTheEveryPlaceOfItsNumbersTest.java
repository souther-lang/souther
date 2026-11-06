package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;
import souther.compiler.partition.NamedElements;
import souther.compiler.partition.OnTheWay;
import souther.compiler.partition.RowDemand;
import souther.compiler.partition.TakenConstraint;
import souther.compiler.partition.WayToTheBorder;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a step leaves a condition a row passed as it was is asked of every place the
 * condition's numbers are read off, and not of which numbers the step names
 * ({@link AnotherLineTheRowsAllow.Reaches}). How often a currency occurs is read off the
 * currencies the elements hold, so a step moving one moves it, and a step that does not hold it
 * says nothing of what it comes to.
 */
class AStepMovesWhatAConditionReadsOffTheEveryPlaceOfItsNumbersTest {

    private static final TermPath FS = TermPath.of("fs");

    private static final NumericTerm CURRENCY = new NumericTerm.ValueOf(
            FS.element().then("currency"));

    private static final NumericTerm OFTEN = NumericTerm.Multiplicity.of(FS,
            FS.element().then("currency"));

    /** That each currency occurs once at most. */
    private static final WayToTheBorder ONCE_AT_MOST = new WayToTheBorder(List.of(
            new OnTheWay.TakenIn(null, new RowDemand.Relational(new TakenConstraint.Affine(
                    new LinearForm<>(ExactRatio.ONE.negated(), Map.of(OFTEN, ExactRatio.ONE)),
                    Rel.LE)), NamedElements.NONE)));

    @Test
    void aStepMovingAPlaceANumberIsReadOffWithoutHoldingItIsTurnedAway() {
        Map<NumericTerm, Place> from = Map.of(CURRENCY, Count.of(0));
        Map<NumericTerm, Place> at = Map.of(CURRENCY, Count.of(1));
        assertFalse(new AnotherLineTheRowsAllow.Reaches(ONCE_AT_MOST, Set.of(CURRENCY))
                .stillArrives(from, at));
    }

    @Test
    void aStepMovingNothingTheConditionReadsLeavesIt() {
        NumericTerm rate = new NumericTerm.ValueOf(TermPath.of("rate"));
        Map<NumericTerm, Place> from = Map.of(rate, Count.of(0));
        Map<NumericTerm, Place> at = Map.of(rate, Count.of(1));
        assertTrue(new AnotherLineTheRowsAllow.Reaches(ONCE_AT_MOST, Set.of(rate))
                .stillArrives(from, at));
    }
}
