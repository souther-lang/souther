package souther.compiler.coverage;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the two sides of a comparison of whole numbers came to is recorded as one visit with the
 * way it came out.
 *
 * <p>One call for the three, so the sides of one visit cannot be put beside the way another came
 * out: a comparison inside a closure handed to a walk is visited once for each element it gets
 * to, and a reading of the run asks which values one visit worked out.
 */
class WhatTheSidesOfAComparisonCameToIsRecordedWithTheVisitTest {

    private static final SiteNumbering NUMBERING =
            Numberings.of(Numberings.Family.COMPARISON, Numberings.Family.COMPARISON);

    @AfterEach
    void stopRecording() {
        Probe.end();
    }

    @Test
    void eachVisitKeepsItsOwnSidesAndItsOwnWay() {
        Probe.begin(NUMBERING.identity());
        Probe.compared(false, 2, 3, 0);
        Probe.compared(true, 3, 3, 0);
        Probe.compared(true, 4, 3, 0);
        AlignedObservation seen = NUMBERING.align(Probe.snapshot());

        ConditionOutcomeSite site = NUMBERING.outcome(0);
        assertEquals(List.of(new SeenComparison(site, 0, 2, 3), new SeenComparison(site, 1, 3, 3),
                new SeenComparison(site, 2, 4, 3)), seen.comparedAt(site));
        assertTrue(seen.sawOnVisit(site, 0, false));
        assertTrue(seen.sawOnVisit(site, 1, true));
        assertTrue(seen.sawOnVisit(site, 2, true));
    }

    /** A condition that hands no sides over keeps none, and counts its visits as before. */
    @Test
    void aConditionWithNoSidesHandedOverKeepsNone() {
        Probe.begin(NUMBERING.identity());
        Probe.condition(true, 1);
        Probe.compared(false, Long.MIN_VALUE, Long.MAX_VALUE, 0);
        AlignedObservation seen = NUMBERING.align(Probe.snapshot());

        assertEquals(List.of(), seen.comparedAt(NUMBERING.outcome(1)));
        assertEquals(List.of(new SeenComparison(NUMBERING.outcome(0), 0, Long.MIN_VALUE,
                Long.MAX_VALUE)), seen.comparedAt(NUMBERING.outcome(0)));
    }

    /** Past the visits kept, nothing is kept: the sides of visit thirty-three would be put beside
     *  no visit at all. */
    @Test
    void onlyTheVisitsKeptKeepTheirSides() {
        Probe.begin(NUMBERING.identity());
        for (int i = 0; i < RecordedVisit.MOST + 5; i++) {
            Probe.compared(true, i, 0, 0);
        }
        List<SeenComparison> kept =
                NUMBERING.align(Probe.snapshot()).comparedAt(NUMBERING.outcome(0));

        assertEquals(RecordedVisit.MOST, kept.size());
        assertEquals(RecordedVisit.MOST - 1, kept.getLast().left());
    }

    /** Sides handed over for a visit that was not recorded are refused where the run is read. */
    @Test
    void sidesOfAVisitThatWasNotRecordedAreRefused() {
        assertThrows(IllegalArgumentException.class, () -> new Observation(NUMBERING.identity(),
                Set.of(), Set.of(), Set.of(), Set.of(), Set.of(),
                Set.of(new RecordedComparison(0, 0, 1, 2))));
    }
}
