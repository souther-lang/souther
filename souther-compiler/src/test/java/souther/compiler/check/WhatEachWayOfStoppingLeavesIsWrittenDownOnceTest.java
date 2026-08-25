package souther.compiler.check;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Which ways of stopping hand the rules to another reading, and which leave them unread.
 *
 * <p>One partition of one enum, written down here so that moving an arm is an edit somebody has to
 * make on purpose. {@link PathEngine#leftBy} is exhaustive, so a way of stopping <em>added</em> is
 * already a compile error; what that does not catch is an arm <em>moved</em> from one side to the
 * other, which changes what several words downstream mean while every switch goes on compiling.
 * That is how the prose in {@link InvariantChecker.Borne} and
 * {@link souther.compiler.values.UnreadReason} came to describe a partition that had moved under it.
 *
 * <p>So the table below is a finding and not a fixture. A diff here is a claim that a stop leaves
 * something different behind, and whoever writes it owes the reason — the words that read
 * {@code leftBy} are what change meaning with it.
 */
class WhatEachWayOfStoppingLeavesIsWrittenDownOnceTest {

    @Test
    void everyWayOfStoppingLeavesWhatIsWrittenHere() {
        Map<GuaranteeWalk.Stop, PathEngine.Leaves> expected = new LinkedHashMap<>();
        // Nothing is declared here to read, so what is written below is written about a value one
        // position down — where a reading of that declaration is opened and a row meets it. The one
        // arm on this side, and the whole of what #1072 turned on.
        expected.put(GuaranteeWalk.Stop.NOTHING_DECLARED, new PathEngine.Leaves.ToAnotherReading());
        // A depth this reader could not afford, a name it was told to suppose holds values, and a
        // field it could find no value for. Each stops where a construction still has to make the
        // value, so a rule under it can refuse the construction.
        expected.put(GuaranteeWalk.Stop.PAST_THE_DEPTH,
                new PathEngine.Leaves.Unread(InvariantChecker.Borne.BY_EVERY_VALUE));
        expected.put(GuaranteeWalk.Stop.ASKED_TO_STOP,
                new PathEngine.Leaves.Unread(InvariantChecker.Borne.BY_EVERY_VALUE));
        expected.put(GuaranteeWalk.Stop.NO_VALUE_THERE,
                new PathEngine.Leaves.Unread(InvariantChecker.Borne.BY_EVERY_VALUE));
        // Read where the name was met, and nothing is opened here — so nobody takes the rules over,
        // and this is not a handing on however much it looks like one.
        expected.put(GuaranteeWalk.Stop.ALREADY_ENTERED,
                new PathEngine.Leaves.Unread(InvariantChecker.Borne.BY_SOME_VALUES));

        Map<GuaranteeWalk.Stop, PathEngine.Leaves> answered = new LinkedHashMap<>();
        for (GuaranteeWalk.Stop stop : GuaranteeWalk.Stop.values()) {
            answered.put(stop, PathEngine.leftBy(stop));
        }

        assertEquals(expected, answered,
                "what each way of stopping leaves is what the words downstream of it mean");
    }

    /**
     * And exactly one of them hands the rules on.
     *
     * <p>Said apart from the table, because it is the fact the words are about rather than a second
     * spelling of them. A second arm on that side is a second way for a position to be discharged
     * by a reading somebody has to have opened, and whoever adds one has to say who opens it.
     */
    @Test
    void oneWayOfStoppingHandsTheRulesToAnotherReading() {
        long handing = java.util.Arrays.stream(GuaranteeWalk.Stop.values())
                .map(PathEngine::leftBy)
                .filter(each -> each instanceof PathEngine.Leaves.ToAnotherReading)
                .count();

        assertEquals(1, handing,
                "each of these is a position somebody has to be shown to have read");
    }
}
