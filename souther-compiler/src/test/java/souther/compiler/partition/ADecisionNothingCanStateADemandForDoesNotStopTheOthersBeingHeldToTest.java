package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A combination of decisions is held to what can be read of them, and a decision no demand can be
 * read for is left to the run rather than keeping the others from being held to anything. In
 * the human-resources example, the filters of a list whose arms state no demand stood beside an age
 * the classes cannot place, and the age was never looked for.
 */
class ADecisionNothingCanStateADemandForDoesNotStopTheOthersBeingHeldToTest {

    private static final HeldOutcome.Bringing UNREAD = new HeldOutcome.Bringing.NothingFound();

    /** One decision with a demand beside one without. */
    @Test
    void theDecisionsADemandCanBeReadForAreHeldToWhateverStandsBesideThem() {
        HeldOutcome.Bringing read = new HeldOutcome.Bringing.Found(
                List.of(HeldOutcomeFixtures.aWayAt("open")), Set.of());

        assertEquals(List.of(read), ReadableDemands.of(List.of(UNREAD, read)).readable());
    }

    @Test
    void theFiguresThatLeftADecisionUnlookedAtCutThePlanAndAskNothingOfARow() {
        ReadableDemands asked = ReadableDemands.of(List.of(new HeldOutcome.Bringing.LeftUnlooked(
                Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG))));

        assertEquals(Set.of(CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG), asked.cutShort());
        assertTrue(asked.readable().isEmpty());
    }

    /** No value on a side one decision comes out on is read, and not left to the run: it is what
     *  says no row holds the decisions together. */
    @Test
    void noValueOnASideADecisionComesOutOnIsReadBesideTheOthers() {
        HeldOutcome.Bringing read = new HeldOutcome.Bringing.Found(
                List.of(HeldOutcomeFixtures.aWayAt("open")), Set.of());
        HeldOutcome.Bringing none = new HeldOutcome.Bringing.NoValueCanStandThere();

        assertEquals(List.of(read, none), ReadableDemands.of(List.of(read, none)).readable());
    }
}
