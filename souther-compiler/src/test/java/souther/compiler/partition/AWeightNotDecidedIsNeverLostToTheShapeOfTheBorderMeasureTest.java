package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.PositionId;
import souther.compiler.inputs.TermPath;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.BoundaryDerivation;
import souther.compiler.query.Measure;
import souther.compiler.query.Measurement;
import souther.compiler.query.OneBorder;
import souther.compiler.query.Weakening;
import souther.compiler.query.WeakeningSet;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the weights of a computation went without reaches the border measure of its behavior
 * whatever the measure came to.
 *
 * <p>A computation is owed its weights whether or not a border of it was drawn, so the borders
 * being none is not the weights having nothing to say. A measure that says no line is drawn has
 * nowhere to say what they went without, and is said only where they went without nothing.
 */
class AWeightNotDecidedIsNeverLostToTheShapeOfTheBorderMeasureTest {

    private static final Weakening WEIGHT = new Weakening.AWeightNotDecided("b",
            OneBorder.derivedValue(), new NumericTerm.ValueOf(TermPath.of("x")),
            Weakening.AWeightNotDecided.Why.NO_BORDER_OF_IT_WAS_READ);

    private static final WeakeningSet WEIGHTS_WENT_WITHOUT = WeakeningSet.of(WEIGHT);

    private static MeasureClosure.OfTheBorder closed() {
        return MeasureClosure.of(List.of(), List.of(), new LinesRead()).border();
    }

    private static Set<ClosureGap> aGap() {
        return Set.of(new ClosureGap.RulesNotReached("b", new PositionId(TermPath.of("x"))));
    }

    private static List<Weakening> causes(Measure<?> measure) {
        return List.copyOf(measure.weakening().causes());
    }

    @Test
    void aClosedReadingDrawingNoLineIsNotApplicableOnlyWhereTheWeightsWentWithoutNothing() {
        assertInstanceOf(MeasureClosure.OfTheBorder.Closed.class, closed());
        assertInstanceOf(Measure.NotApplicable.class,
                BoundaryDerivation.of(List.<BorderAssessment>of(), WeakeningSet.none(), closed(),
                        null));

        Measure<List<BorderAssessment>> said = BoundaryDerivation.of(List.of(),
                WEIGHTS_WENT_WITHOUT, closed(), null);
        assertInstanceOf(Measurement.Partial.class, said);
        assertEquals(List.of(WEIGHT), causes(said));
    }

    @Test
    void aReadingStoppedShortWithNoLineDrawnStillSaysWhatTheWeightsWentWithout() {
        Measure<List<BorderAssessment>> open = BoundaryDerivation.of(List.of(),
                WEIGHTS_WENT_WITHOUT, new MeasureClosure.OfTheBorder.Open(aGap()), null);
        assertInstanceOf(Measurement.FailedToMeasure.class, open);
        assertTrue(causes(open).contains(WEIGHT), causes(open).toString());

        Measure<List<BorderAssessment>> unread = BoundaryDerivation.of(List.of(),
                WEIGHTS_WENT_WITHOUT, new MeasureClosure.OfTheBorder.BodyNotRead("b", Set.of()),
                null);
        assertInstanceOf(Measurement.FailedToMeasure.class, unread);
        assertTrue(causes(unread).contains(WEIGHT), causes(unread).toString());
    }
}
