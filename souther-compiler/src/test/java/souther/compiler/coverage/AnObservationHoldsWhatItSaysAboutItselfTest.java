package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a record of a run may say, held where the record is made rather than where it is written.
 *
 * <p>The one producer today records a comparison being reached and the way it came out in a single
 * call, so nothing it makes can break this. That is how the producer is written and producers get
 * rewritten; what every reader of a run is entitled to is that the two agree, because a claim about
 * a place is certified against exactly that.
 *
 * <p>Both directions, because either half alone is a value a reader is answered wrongly from. A way
 * out of a place the run says it never reached certifies a claim about somewhere it was not; a
 * place the run reached that no way out is recorded for reads as a comparison nothing evaluated,
 * which is what a row that short-circuited past it looks like.
 */
class AnObservationHoldsWhatItSaysAboutItselfTest {

    /** A comparison at 0 and an arm at 1, so a number of each family is in play and the numbering
     *  can be asked which is which. */
    private static final SiteNumbering NUMBERING =
            Numberings.of(Numberings.Family.COMPARISON, Numberings.Family.ARM);

    private static final NumberingIdentity UNDER = NUMBERING.identity();

    @Test
    void awayOutOfAComparisonMeansTheComparisonWasReached() {
        ComparisonOutcome held = new ComparisonOutcome(0, true);

        assertThrows(IllegalArgumentException.class,
                () -> new Observation(UNDER, Set.of(), Set.of(held)),
                "a run that saw a comparison come out one way reached it");
        assertTrue(new Observation(UNDER, Set.of(0), Set.of(held)).comparisons().contains(held),
                "and one that holds both says so");
    }

    /**
     * And a comparison reached is one that came out some way.
     *
     * <p>The same call records both, so a run holding the number and no way out of it is one
     * nothing produces. Left unheld, such a run reads as a comparison that was never evaluated —
     * the answer a row which short-circuited past it gives — and the two would be one.
     */
    @Test
    void aComparisonReachedMeansAWayOutOfItWasRecorded() {
        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> new Observation(UNDER, Set.of(0), Set.of()));

        assertTrue(refused.getMessage().contains("come out some way"), refused.getMessage());
    }

    /** And an arm reached is just an arm reached: what a fork's arm has is no way out to record. */
    @Test
    void anArmReachedIsNotHeldToHavingComeOutAnyWay() {
        assertTrue(new Observation(UNDER, Set.of(1), Set.of()).taken().contains(1),
                "which is what says the rule above is about the comparisons");
    }

    /**
     * Both ways out of one comparison are not a contradiction.
     *
     * <p>A place a run comes back to is evaluated more than once and may come out either way on
     * different times round. A record that refused to hold both would be saying less than the run
     * showed, which is the opposite of what it is for.
     */
    @Test
    void bothWaysOutOfOneComparisonAreARunThatCameBackToIt() {
        Observation seen = new Observation(UNDER, Set.of(0),
                Set.of(new ComparisonOutcome(0, true), new ComparisonOutcome(0, false)));

        assertTrue(seen.comparisons().contains(new ComparisonOutcome(0, true)));
        assertTrue(seen.comparisons().contains(new ComparisonOutcome(0, false)));
    }
}
