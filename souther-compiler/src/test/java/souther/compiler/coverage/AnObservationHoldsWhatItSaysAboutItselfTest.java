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
 * rewritten; what every reader of a run is entitled to is that a way out of a comparison means the
 * comparison was reached, because a claim about a place is certified against exactly that.
 */
class AnObservationHoldsWhatItSaysAboutItselfTest {

    @Test
    void awayOutOfAComparisonMeansTheComparisonWasReached() {
        ComparisonOutcome held = new ComparisonOutcome(7, true);
        NumberingIdentity under = NumberingIdentity.of("fixture");

        assertThrows(IllegalArgumentException.class,
                () -> new Observation(under, Set.of(), Set.of(held)),
                "a run that saw a comparison come out one way reached it");
        assertTrue(new Observation(under, Set.of(7), Set.of(held)).comparisons().contains(held),
                "and one that holds both says so");
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
        Observation seen = new Observation(NumberingIdentity.of("fixture"), Set.of(3),
                Set.of(new ComparisonOutcome(3, true), new ComparisonOutcome(3, false)));

        assertTrue(seen.comparisons().contains(new ComparisonOutcome(3, true)));
        assertTrue(seen.comparisons().contains(new ComparisonOutcome(3, false)));
    }
}
