package souther.compiler.coverage;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the two sides of a comparison of whole numbers came to is recorded as one visit with the
 * way it came out, and the recording says where it stopped keeping visits.
 *
 * <p>One call for the three, so the sides of one visit cannot be put beside the way another came
 * out: a comparison inside a closure handed to a walk is visited once for each element it gets
 * to, and a reading of the run asks which values one visit worked out. And whether every visit
 * was kept is the recording's word, never a count: a run that visited as many times as are kept
 * kept them all.
 */
class WhatTheSidesOfAComparisonCameToIsRecordedWithTheVisitTest {

    private static final SiteNumbering NUMBERING =
            Numberings.of(Numberings.Family.COMPARISON, Numberings.Family.COMPARISON);

    @AfterEach
    void stopRecording() {
        Probe.end();
    }

    /** A run visiting the comparison at site 0 {@code times} times, its sides a count apiece. */
    private static AlignedObservation visited(int times) {
        Probe.begin(NUMBERING.identity());
        for (int i = 0; i < times; i++) {
            Probe.compared(true, i, 0, 0);
        }
        return NUMBERING.align(Probe.snapshot());
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

    /** As many visits as are kept is every visit kept, and one more is not. */
    @Test
    void aRunVisitingAsOftenAsIsKeptKeptEveryVisit() {
        ConditionOutcomeSite site = NUMBERING.outcome(0);

        AlignedObservation exactly = visited(RecordedVisit.MOST);
        assertEquals(RecordedVisit.MOST, exactly.comparedAt(site).size());
        assertTrue(exactly.keptEveryVisit(site));

        AlignedObservation past = visited(RecordedVisit.MOST + 1);
        assertEquals(RecordedVisit.MOST, past.comparedAt(site).size());
        assertEquals(RecordedVisit.MOST - 1, past.comparedAt(site).getLast().left());
        assertFalse(past.keptEveryVisit(site));
    }

    /** Each place says where it stopped keeping for itself. */
    @Test
    void whereARunStoppedKeepingIsSaidOfEachPlace() {
        Probe.begin(NUMBERING.identity());
        for (int i = 0; i < RecordedVisit.MOST + 1; i++) {
            Probe.compared(true, i, 0, 0);
        }
        for (int i = 0; i < RecordedVisit.MOST; i++) {
            Probe.compared(true, i, 0, 1);
        }
        AlignedObservation seen = NUMBERING.align(Probe.snapshot());

        assertFalse(seen.keptEveryVisit(NUMBERING.outcome(0)));
        assertTrue(seen.keptEveryVisit(NUMBERING.outcome(1)));
    }

    /** Sides handed over for a visit that was not recorded are refused where the run is read. */
    @Test
    void sidesOfAVisitThatWasNotRecordedAreRefused() {
        assertThrows(IllegalArgumentException.class, () -> new Observation(NUMBERING.identity(),
                Set.of(), Set.of(), Set.of(), Set.of(), Set.of(),
                Set.of(new RecordedComparison(0, 0, 1, 2)), Set.of()));
    }

    /** A place said to be visited past the kept had every visit kept recorded first. */
    @Test
    void aPlaceVisitedPastTheKeptWithFewerKeptIsRefused() {
        assertThrows(IllegalArgumentException.class, () -> new Observation(NUMBERING.identity(),
                Set.of(), Set.of(new RecordedConditionOutcome(0, true)),
                Set.of(new RecordedVisit(0, 0, true)), Set.of(), Set.of(), Set.of(), Set.of(0)));
    }
}
