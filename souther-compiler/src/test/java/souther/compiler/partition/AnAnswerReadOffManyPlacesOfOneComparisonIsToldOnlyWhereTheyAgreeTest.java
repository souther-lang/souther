package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.coverage.AlignedObservation;
import souther.compiler.coverage.ConditionOutcomeSite;
import souther.compiler.coverage.Numberings;
import souther.compiler.coverage.Runs;
import souther.compiler.coverage.SeenConditionOutcome;
import souther.compiler.coverage.SiteNumbering;

import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * What a run's record says of a comparison made at several places, for a point of a class the line
 * cuts.
 *
 * <p>The places are the copies of one comparison, and the record is of a place and not of the
 * element a reading chose. An answer at one place is no answer for the element while another place
 * answered the other way, so every place is read before any answer is given, and the answer is
 * told only where they agree.
 */
class AnAnswerReadOffManyPlacesOfOneComparisonIsToldOnlyWhereTheyAgreeTest {

    private static final SiteNumbering NUMBERING = Numberings.ofComparisons(2);

    private static final ConditionOutcomeSite ONE = NUMBERING.outcome(0);

    private static final ConditionOutcomeSite ANOTHER = NUMBERING.outcome(1);

    private static final List<ConditionOutcomeSite> BOTH = List.of(ONE, ANOTHER);

    private static StandingAtAPoint.Arrived read(AlignedObservation run, boolean holds) {
        return StandingAtAPoint.arrivedAt(BOTH, Optional.of(holds), run);
    }

    private static AlignedObservation saw(SeenConditionOutcome... outcomes) {
        return Runs.of(NUMBERING, Set.of(), Set.of(outcomes));
    }

    @Test
    void placesThatAllCameOutAsTheClassSaysAreTheAnswer() {
        AlignedObservation run = saw(new SeenConditionOutcome(ONE, true),
                new SeenConditionOutcome(ANOTHER, true));

        assertEquals(StandingAtAPoint.Arrived.MATCHED, read(run, true));
    }

    @Test
    void aPlaceNothingWasRecordedAtDoesNotTakeTheAnswerFromTheOther() {
        AlignedObservation run = saw(new SeenConditionOutcome(ANOTHER, true));

        assertEquals(StandingAtAPoint.Arrived.MATCHED, read(run, true));
    }

    @Test
    void oneAnsweringAsTheClassSaysAndTheOtherTheOtherWayIsNotTold() {
        AlignedObservation run = saw(new SeenConditionOutcome(ONE, true),
                new SeenConditionOutcome(ANOTHER, false));

        assertInstanceOf(StandingAtAPoint.Arrived.Untold.class, read(run, true),
                "the first place says nothing of which application belongs to the element");
        assertInstanceOf(StandingAtAPoint.Arrived.Untold.class, read(run, false),
                "and the same record is not told for the other class either");
    }

    @Test
    void onePlaceThatCameOutBothWaysIsNotTold() {
        AlignedObservation run = saw(new SeenConditionOutcome(ONE, true),
                new SeenConditionOutcome(ONE, false));

        assertInstanceOf(StandingAtAPoint.Arrived.Untold.class, read(run, true));
    }

    @Test
    void placesThatAllCameOutTheOtherWayMissTheClass() {
        AlignedObservation run = saw(new SeenConditionOutcome(ONE, false),
                new SeenConditionOutcome(ANOTHER, false));

        assertEquals(StandingAtAPoint.Arrived.MISSED, read(run, true));
    }

    @Test
    void aRunRecordedAtNoPlaceMissesTheClass() {
        assertEquals(StandingAtAPoint.Arrived.MISSED, read(Runs.nowhere(NUMBERING), true));
    }

    @Test
    void asksOfNoClassOnlyWhetherTheComparisonWasMade() {
        AlignedObservation mixed = saw(new SeenConditionOutcome(ONE, true),
                new SeenConditionOutcome(ANOTHER, false));

        assertEquals(StandingAtAPoint.Arrived.MATCHED,
                StandingAtAPoint.arrivedAt(BOTH, Optional.empty(), mixed),
                "the answers it came out with do not matter to a point against the line");
        assertEquals(StandingAtAPoint.Arrived.MISSED,
                StandingAtAPoint.arrivedAt(BOTH, Optional.empty(), Runs.nowhere(NUMBERING)));
    }
}
