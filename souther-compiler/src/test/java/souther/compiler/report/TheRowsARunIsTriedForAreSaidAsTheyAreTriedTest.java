package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.CompositionRepertoire;
import souther.compiler.partition.RowsARunIsTriedFor;
import souther.compiler.publish.CanonicalSelection;
import souther.compiler.publish.PublicationOrders;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The population the report says the rows a run is tried for are is built from the figures the
 * candidates are written with, so a figure moved changes the report with it.
 */
class TheRowsARunIsTriedForAreSaidAsTheyAreTriedTest {

    private static String said() {
        CanonicalSelection<CompositionRepertoire> only = PublicationOrders.COMPOSITION_REPERTOIRES
                .keep(Set.of(CompositionRepertoire.ROWS_A_RUN_IS_TRIED_FOR));
        return Reasons.writes(only);
    }

    @Test
    void theLargestContainerAndEveryValueTriedAreNamed() {
        String said = said();
        assertTrue(said.contains("0 to " + RowsARunIsTriedFor.mostElements() + " copies"), said);
        for (long value : RowsARunIsTriedFor.values()) {
            assertTrue(said.contains(String.valueOf(value)), "value " + value + " in: " + said);
        }
    }

    @Test
    void theSentenceSaysWhatTheCandidatesAreWrittenAt() {
        String said = said();
        assertTrue(said.contains("one element"), said);
        assertTrue(said.contains("plain value"), said);
        assertTrue(said.contains("outside a container"), said);
    }
}
