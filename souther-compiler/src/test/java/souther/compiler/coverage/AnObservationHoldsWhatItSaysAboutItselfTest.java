package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A number a run holds is one the numbering issued to the family it is recorded under.
 *
 * <p>The two families take their numbers from one counter, so nothing in a number says which of
 * them it was written for. What says it is which call wrote it down — and the recording keeps them
 * apart, so the answer is the record's own rather than something a reader works out afterwards by
 * asking the numbering about a set holding both.
 *
 * <p>Held where the recording is made rather than where it is read. A number written into the wrong
 * family is the emitter having lit a place it was not at, and a reader meeting it later has a run
 * saying something no run could say: an arm no arm was ever emitted for, or a comparison that never
 * came out any way at all.
 *
 * <p>What is <em>not</em> held here, said rather than left to be looked for: nothing relates the two
 * sets. A comparison is recorded by the way it came out and by nothing else, so there is no second
 * record of it to agree with — which is what makes each of them mean something on its own.
 */
class AnObservationHoldsWhatItSaysAboutItselfTest {

    /** A comparison at 0 and an arm at 1, so each family has a number the other does not. */
    private static final SiteNumbering NUMBERING =
            Numberings.of(Numberings.Family.COMPARISON, Numberings.Family.ARM);

    private static final NumberingIdentity UNDER = NUMBERING.identity();

    @Test
    void aComparisonsNumberIsNotAnArmARunPassed() {
        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> new Observation(UNDER, Set.of(0), Set.of()));

        assertTrue(refused.getMessage().contains("recorded as an arm"), refused.getMessage());
    }

    @Test
    void anArmsNumberIsNoComparisonARunEvaluated() {
        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> new Observation(UNDER, Set.of(),
                        Set.of(new ComparisonOutcome(1, true))));

        assertTrue(refused.getMessage().contains("recorded as a comparison"),
                refused.getMessage());
    }

    /** And each family holds its own, which is what says the refusals above are about the family
     *  and not about holding anything at all. */
    @Test
    void andEachFamilyHoldsItsOwn() {
        Observation seen = new Observation(UNDER, Set.of(1),
                Set.of(new ComparisonOutcome(0, true)));

        assertTrue(seen.arms().contains(1));
        assertTrue(seen.comparisons().contains(new ComparisonOutcome(0, true)));
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
        Observation seen = new Observation(UNDER, Set.of(),
                Set.of(new ComparisonOutcome(0, true), new ComparisonOutcome(0, false)));

        assertTrue(seen.comparisons().contains(new ComparisonOutcome(0, true)));
        assertTrue(seen.comparisons().contains(new ComparisonOutcome(0, false)));
    }
}
