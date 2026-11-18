package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.ReadingState.Restore;
import souther.compiler.partition.ReadingState.Scoped;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A ledger's revision says which history of additions it stands at, and a checkpoint is rewound to
 * only while it is on that history ({@link Ledger}).
 *
 * <p>A revision stands in for what a ledger holds wherever a reading is compared before and after
 * it is made, so it must differ wherever what the ledger holds could: after any addition, inside a
 * group as well, and on another branch from the same place however many entries that branch added.
 */
class ALedgerSaysWhichHistoryItStandsAtTest {

    @Test
    void twoBranchesFromOneCheckpointThatAddedAsManyStandAtDifferentRevisions() {
        Ledger.OfEntries<String> ledger = new Ledger.OfEntries<>();
        Ledger.Checkpoint parting = ledger.checkpoint();

        ledger.add("alpha");
        Object one = ledger.mark();
        ledger.rewind(parting);
        ledger.add("beta");

        assertNotEquals(one, ledger.mark(), "one entry each, and not the same entry");
    }

    @Test
    void addingAndTakingItOffAgainLeavesTheLedgerWhereItWas() {
        Ledger.OfEntries<String> ledger = new Ledger.OfEntries<>();
        ledger.add("alpha");
        Object before = ledger.mark();
        Ledger.Checkpoint checkpoint = ledger.checkpoint();

        ledger.add("beta");
        assertNotEquals(before, ledger.mark());
        ledger.rewind(checkpoint);

        assertEquals(before, ledger.mark());
        assertEquals(List.of("alpha"), ledger.view());
    }

    @Test
    void aCheckpointOnABranchRewoundPastIsRefused() {
        Ledger.OfEntries<String> ledger = new Ledger.OfEntries<>();
        Ledger.Checkpoint parting = ledger.checkpoint();
        ledger.add("alpha");
        Ledger.Checkpoint onTheBranch = ledger.checkpoint();
        ledger.rewind(parting);
        ledger.add("beta");

        assertThrows(IllegalStateException.class, () -> ledger.rewind(onTheBranch),
                "taking entries off cannot put back alpha");
        assertEquals(List.of("beta"), ledger.view());
    }

    @Test
    void aCheckpointOfAnotherLedgerIsRefused() {
        Ledger.OfEntries<String> one = new Ledger.OfEntries<>();
        Ledger.OfEntries<String> other = new Ledger.OfEntries<>();

        assertThrows(IllegalStateException.class, () -> other.rewind(one.checkpoint()));
    }

    @Test
    void twoLedgersThatHoldTheSameStandAtDifferentRevisions() {
        Ledger.OfEntries<String> one = new Ledger.OfEntries<>();
        Ledger.OfEntries<String> other = new Ledger.OfEntries<>();
        one.add("alpha");
        other.add("alpha");

        assertNotEquals(one.mark(), other.mark(),
                "a revision identifies a history, and these are two");
    }

    @Test
    void somethingAddedUnderAKeyThatHoldsSomethingAlreadyMovesTheRevision() {
        Ledger.Grouped<String, String> grouped = new Ledger.Grouped<>();
        grouped.add("count", "xs");
        Object before = grouped.mark();
        Ledger.Checkpoint checkpoint = grouped.checkpoint();

        grouped.add("count", "ys");
        assertNotEquals(before, grouped.mark(), "the keys are as many as they were");
        assertEquals(List.of("xs", "ys"), grouped.under("count"));

        grouped.add("another", "zs");
        grouped.rewind(checkpoint);
        assertEquals(List.of("xs"), grouped.under("count"));
        assertEquals(List.of("count"), List.copyOf(grouped.keys()));
    }

    @Test
    void aKeyAlreadyHeldAddsNothingAndRewindingTakesOffOnlyTheKeysAfter() {
        Ledger.Keyed<String, Integer> keyed = new Ledger.Keyed<>();
        keyed.putIfAbsent("first", 1);
        Ledger.Checkpoint checkpoint = keyed.checkpoint();
        Object before = keyed.mark();

        assertEquals(1, keyed.putIfAbsent("first", 2));
        assertEquals(before, keyed.mark(), "the first value put under a key is the one it keeps");

        keyed.putIfAbsent("second", 3);
        keyed.rewind(checkpoint);
        assertEquals(Map.of("first", 1), keyed.view());
    }

    @Test
    void whatALedgerHandsOutCannotBeChangedThrough() {
        Ledger.OfEntries<String> entries = new Ledger.OfEntries<>();
        Ledger.Keyed<String, Integer> keyed = new Ledger.Keyed<>();
        Ledger.Grouped<String, String> grouped = new Ledger.Grouped<>();
        grouped.add("count", "xs");

        assertThrows(UnsupportedOperationException.class, () -> entries.view().add("alpha"));
        assertThrows(UnsupportedOperationException.class, () -> keyed.view().put("k", 1));
        assertThrows(UnsupportedOperationException.class, () -> keyed.keys().add("k"));
        assertThrows(UnsupportedOperationException.class,
                () -> grouped.under("count").add("ys"));
    }

    @Test
    void aReadingThatAddedToALedgerItMustLeaveAloneIsSeenAndOneThatTookItOffIsNot() {
        ReadingState state = new ReadingState();
        Scoped<Ledger.OfEntries<String>> collected = state.writtenInto();
        Ledger.OfEntries<String> ledger = new Ledger.OfEntries<>();
        try (Restore _ = collected.set(ledger)) {
            List<Object[]> before = state.guards();
            Ledger.Checkpoint checkpoint = ledger.checkpoint();

            ledger.add("alpha");
            assertFalse(state.sameGuards(before, state.guards()));

            ledger.rewind(checkpoint);
            assertTrue(state.sameGuards(before, state.guards()));
        }
    }

    /**
     * Across readings a ledger is another object each time it is made, so what it holds is
     * compared by what it holds: two ledgers holding the same are the same input to a reading that
     * asked what it holds.
     */
    @Test
    void twoLedgersHoldingTheSameAreTheSameInputToAReadingThatAskedWhatTheyHold() {
        ReadingState state = new ReadingState();
        Scoped<Ledger.OfEntries<String>> answers = state.writtenIntoAndAskedAfter();
        String element = "alpha";
        Ledger.OfEntries<String> one = new Ledger.OfEntries<>();
        one.add(element);
        Ledger.OfEntries<String> other = new Ledger.OfEntries<>();
        other.add(element);
        ReadingState.Inputs then;
        try (Restore _ = answers.set(one)) {
            then = state.inputs();
        }
        int before = state.startConsulting();
        answers.contents();
        int asked = state.endConsulting(before);

        try (Restore _ = answers.set(other)) {
            assertTrue(state.sameInputs(then, state.inputs(), false, asked));
            other.add("beta");
            assertFalse(state.sameInputs(then, state.inputs(), false, asked));
        }
    }

    @Test
    void anInputComparedByValueThatIsALedgerIsComparedByWhatItHolds() {
        ReadingState state = new ReadingState();
        Scoped<Ledger.Keyed<String, Integer>> counting = state.guarded();
        Ledger.Keyed<String, Integer> one = new Ledger.Keyed<>();
        one.putIfAbsent("count", 1);
        Ledger.Keyed<String, Integer> other = new Ledger.Keyed<>();
        other.putIfAbsent("count", 1);
        ReadingState.Inputs then;
        try (Restore _ = counting.set(one)) {
            then = state.inputs();
            one.putIfAbsent("another", 2);
            assertFalse(state.sameInputs(then, state.inputs(), false, 0),
                    "a later addition is not in what was taken");
        }

        try (Restore _ = counting.set(other)) {
            assertTrue(state.sameInputs(then, state.inputs(), false, 0));
        }
    }
}
