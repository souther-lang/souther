package souther.compiler.coverage;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;

import java.util.Arrays;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A condition a run visits more than once is recorded by which visit came out which way.
 *
 * <p>The ways it came out are a set, and a run that had it hold on the first visit and fail on the
 * second records the same set as one that did the opposite. What tells them apart is the visit, and
 * the recording counts the visits itself because the probed class writes the same call at each.
 */
class AConditionVisitedAgainIsRecordedPerVisitTest {

    private static final SiteNumbering NUMBERING =
            Numberings.of(Numberings.Family.COMPARISON, Numberings.Family.COMPARISON);

    @AfterEach
    void stopRecording() {
        Probe.end();
    }

    private static AlignedObservation ran(boolean... answers) {
        Probe.begin(NUMBERING.identity());
        for (boolean held : answers) {
            Probe.condition(held, 0);
        }
        return NUMBERING.align(Probe.snapshot());
    }

    @Test
    void theOrderTheWaysCameOutInIsWhatTellsTwoRunsApart() {
        AlignedObservation holdsThenFails = ran(true, false);
        AlignedObservation failsThenHolds = ran(false, true);

        ConditionOutcomeSite site = NUMBERING.outcome(0);
        assertEquals(holdsThenFails.outcomes(), failsThenHolds.outcomes(),
                "the ways alone cannot tell them apart");
        assertTrue(holdsThenFails.sawOnVisit(site, 0, true));
        assertTrue(holdsThenFails.sawOnVisit(site, 1, false));
        assertFalse(holdsThenFails.sawOnVisit(site, 0, false));
        assertFalse(holdsThenFails.sawOnVisit(site, 1, true));
        assertTrue(failsThenHolds.sawOnVisit(site, 0, false));
        assertTrue(failsThenHolds.sawOnVisit(site, 1, true));
    }

    @Test
    void aVisitNobodyMadeIsNotSeen() {
        assertFalse(ran(true).sawOnVisit(NUMBERING.outcome(0), 1, true));
    }

    /** A claim names only a visit a recording could answer. */
    @Test
    void aClaimCannotNameAVisitPastThoseTheRecordingKeeps() {
        assertThrows(IllegalArgumentException.class,
                () -> new ControlClaim.Visit.Nth(RecordedVisit.MOST));
        assertThrows(IllegalArgumentException.class, () -> new ControlClaim.Visit.Nth(-1));
        assertEquals(RecordedVisit.MOST - 1,
                new ControlClaim.Visit.Nth(RecordedVisit.MOST - 1).index());
    }

    /** The count of visits stops where the recording does, so it cannot come round to a visit
     *  already past. */
    @Test
    void visitsAreNotRecordedAgainAfterTheCountHasPassedWhatIsKept() {
        Probe.begin(NUMBERING.identity());
        for (int i = 0; i < RecordedVisit.MOST; i++) {
            Probe.condition(true, 0);
        }
        for (int i = 0; i < 10 * RecordedVisit.MOST; i++) {
            Probe.condition(false, 0);
        }
        AlignedObservation seen = NUMBERING.align(Probe.snapshot());

        for (int visit = 0; visit < RecordedVisit.MOST; visit++) {
            assertTrue(seen.sawOnVisit(NUMBERING.outcome(0), visit, true));
            assertFalse(seen.sawOnVisit(NUMBERING.outcome(0), visit, false));
        }
    }

    @Test
    void aVisitTheRecordingDoesNotKeepIsRefusedRatherThanAnsweredNo() {
        assertThrows(IllegalArgumentException.class,
                () -> ran(true).sawOnVisit(NUMBERING.outcome(0), RecordedVisit.MOST, true));
    }

    @Test
    void eachConditionIsCountedOnItsOwn() {
        Probe.begin(NUMBERING.identity());
        Probe.condition(true, 0);
        Probe.condition(false, 1);
        Probe.condition(false, 0);
        AlignedObservation seen = NUMBERING.align(Probe.snapshot());

        assertTrue(seen.sawOnVisit(NUMBERING.outcome(0), 1, false));
        assertTrue(seen.sawOnVisit(NUMBERING.outcome(1), 0, false));
    }

    /** The recording grows with the numbers it is handed, and what it held before is kept. */
    @Test
    void aConditionNumberedPastWhatTheRecordingStartedWithIsRecordedAsAny() {
        Numberings.Family[] families = new Numberings.Family[300];
        Arrays.fill(families, Numberings.Family.COMPARISON);
        SiteNumbering many = Numberings.of(families);
        Probe.begin(many.identity());
        Probe.condition(true, 0);
        Probe.condition(false, 299);
        Probe.condition(true, 299);
        AlignedObservation seen = many.align(Probe.snapshot());

        assertTrue(seen.sawOnVisit(many.outcome(0), 0, true));
        assertTrue(seen.sawOnVisit(many.outcome(299), 0, false));
        assertTrue(seen.sawOnVisit(many.outcome(299), 1, true));
        assertFalse(seen.sawOnVisit(many.outcome(299), 0, true));
        assertTrue(seen.saw(many.outcome(299), true));
    }

    @Test
    void onlyTheFirstVisitsAreRecorded() {
        boolean[] answers = new boolean[RecordedVisit.MOST + 3];
        answers[RecordedVisit.MOST + 1] = true;
        AlignedObservation seen = ran(answers);

        assertTrue(seen.sawOnVisit(NUMBERING.outcome(0), RecordedVisit.MOST - 1, false));
        assertTrue(seen.saw(NUMBERING.outcome(0), true),
                "a visit past the figure is still a way the condition came out");
    }
}
