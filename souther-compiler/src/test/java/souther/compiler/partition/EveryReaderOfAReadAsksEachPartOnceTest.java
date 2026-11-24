package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ReadersOfAGraph;
import souther.compiler.types.ModelOccurrences;
import souther.test.ClosedWorldContract;

import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every reader of what a condition asks of a row asks each part of it once, however many
 * alternatives hold it.
 *
 * <p>What a condition asks is one of several things where a name was used twice, so the reads are
 * a graph and the ways down a chain of them are two to its length ({@link ReadersOfAGraph}). Asked
 * of a chain of reads each holding the one before it in both alternatives.
 */
@ClosedWorldContract
class EveryReaderOfAReadAsksEachPartOnceTest {

    /** Readers whose work is the ways down, which is what they are for. */
    private static final Map<String, String> BY_THEIR_NATURE = Map.of(
            "DemandReading$Read$OneOf.toString", "the text of the read");

    /** How many readers are asked at least, so that finding none is not a pass. */
    private static final int AT_LEAST_ASKED = 5;

    /** Each read holds the one before it in both alternatives, and a way of its own in one. */
    private static DemandReading.Read chainOf(int length) {
        DemandReading.Read held = new DemandReading.Read.Settled(true);
        for (int at = 1; at <= length; at++) {
            held = new DemandReading.Read.OneOf(List.of(List.of(held),
                    List.of(held, new DemandReading.Read.Settled(at % 2 == 0))),
                    Optional.empty());
        }
        return held;
    }

    @Test
    void noReaderOfWhatAConditionAsksGoesDownEveryWayToItsParts() throws Exception {
        ReadersOfAGraph.Findings found = ReadersOfAGraph.askEach(List.of(
                new ReadersOfAGraph.Chain("reads", DemandReading.Read.class,
                        EveryReaderOfAReadAsksEachPartOnceTest::chainOf, Map.of(
                        DemandReading.Read.class, () -> new DemandReading.Read.Settled(true),
                        DemandReading.ReadOff.class, () -> new DemandReading.ReadOff(
                                new IdentityHashMap<>(), ModelOccurrences.NONE)))),
                BY_THEIR_NATURE);

        assertEquals(Set.of(), found.slow());
        assertTrue(found.answered().size() >= AT_LEAST_ASKED, found.answered().size() + " readers asked");
    }
}
