package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.publish.PublicationOrders;
import souther.compiler.reach.WhatMayStopARun;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A point no row is at, which something shows a value can stand at, and the way to which may stop
 * a run on values this compiler does not say, is open on whether a row there can be written — and
 * is no gap.
 *
 * <p>What showed a value at the point shows nothing of a run getting there with it. Read as a gap,
 * a build would refuse over a row nothing shows any run reaches; left out of the count, the point
 * would leave it as this compiler read less. So it is counted, undecided, and says why. Where the
 * body says every row there aborts, that is said instead, as the stronger of the two.
 */
class APointTheWayToWhichMayStopIsOpenAndNoGapTest {

    private static WritabilityKnowledge established() {
        return new WritabilityKnowledge.Established(ItemAssessment.WritabilityEvidence.of(
                Set.of(ItemAssessment.WritabilityEvidence.Ground.IT_IS_PROVED)));
    }

    @Test
    void aMissedPointPastSomethingThatMayStopIsUndecidedOnTheWayThere() {
        ObligationDisposition disposition = ObligationDisposition.of(
                new ObligationCoverage.Missed(), established(),
                ObligationDisposition.openOn(List.of(),
                        List.of(new WhatMayStopARun.AnOperator())));
        assertEquals(List.of(new ObligationDisposition.Uncertainty.WhetherARowCanBeWritten
                        .TheWayThereMayStop(PublicationOrders.WHAT_MAY_STOP_A_RUN.keep(
                                List.of(new WhatMayStopARun.AnOperator())))),
                ((ObligationDisposition.Undecided) disposition).because().written());
    }

    @Test
    void aMissedPointWithNothingOnTheWayThatMayStopIsAGap() {
        assertTrue(ObligationDisposition.of(new ObligationCoverage.Missed(), established(),
                ObligationDisposition.openOn(List.of(), List.of()))
                instanceof ObligationDisposition.Unmet);
    }

    @Test
    void aPointARowStandsAtIsMetWhatMayStopOnTheWay() {
        assertTrue(ObligationDisposition.of(new ObligationCoverage.Witnessed(RowWitnesses.ANOTHER_ROW), established(),
                ObligationDisposition.openOn(List.of(), List.of(new WhatMayStopARun.ACall())))
                instanceof ObligationDisposition.Met);
    }
}
