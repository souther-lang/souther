package souther.compiler.check;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * How much of what stands at a position the rules a stop leaves unread are about.
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
 *
 * <p><b>No way of stopping hands the rules to another reading, and that is javac's to say.</b>
 * Whether a position's rules belong to a reading opened elsewhere is
 * {@link TypeGuarantees.At.HandedOn}, answered by the reading and said beside what was read, and
 * {@code leftBy} answers a {@link InvariantChecker.Borne}. A position that both states rules and
 * leaves something below to another reading — a sum whose cases share a spread is one — has no
 * single arm to be, so the two are not one enum.
 */
class WhatEachWayOfStoppingLeavesIsWrittenDownOnceTest {

    @Test
    void everyWayOfStoppingLeavesWhatIsWrittenHere() {
        Map<GuaranteeWalk.Stop, InvariantChecker.Borne> expected = new LinkedHashMap<>();
        // A depth this reader could not afford, and a name it was told to suppose holds values.
        // Each stops where a construction still has to make the value, so a rule under it can refuse
        // the construction.
        expected.put(GuaranteeWalk.Stop.PAST_THE_DEPTH, InvariantChecker.Borne.BY_EVERY_VALUE);
        expected.put(GuaranteeWalk.Stop.ASKED_TO_STOP, InvariantChecker.Borne.BY_EVERY_VALUE);
        // Read where the name was met, and nothing is opened here — so nobody takes the rules over,
        // and this is not a handing on however much it looks like one.
        expected.put(GuaranteeWalk.Stop.ALREADY_ENTERED, InvariantChecker.Borne.BY_SOME_VALUES);

        Map<GuaranteeWalk.Stop, InvariantChecker.Borne> answered = new LinkedHashMap<>();
        for (GuaranteeWalk.Stop stop : GuaranteeWalk.Stop.values()) {
            answered.put(stop, PathEngine.leftBy(stop));
        }

        assertEquals(expected, answered,
                "what each way of stopping leaves is what the words downstream of it mean");
    }
}
