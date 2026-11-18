package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.ReadingState.Restore;
import souther.compiler.partition.ReadingState.Scoped;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An input a reading writes into stands as it did where it is there or is not, and, where the
 * reading asked what it holds, where it holds what it did ({@link ReadingState#sameInputs}).
 *
 * <p>Whether a ledger is there says nothing of what is in it, and a reading that goes through what
 * is in it ({@code isEmpty}, each entry) depends on that: taken where another ledger is, with the
 * same being there, it would come to what the other ledger does not say. A ledger of values
 * gathered under keys is asked what is gathered under each key too.
 */
class AnInputWrittenIntoIsComparedByWhatItHoldsOnlyWhereTheReadingAskedAfterItTest {

    private final ReadingState state = new ReadingState();
    private final Scoped<Ledger.OfEntries<String>> answers = state.writtenIntoAndAskedAfter();
    private final Scoped<Ledger.Grouped<String, String>> counts =
            state.writtenIntoAndAskedAfter();

    /** What a reading that does nothing but {@code asking} has asked after. */
    private int askedBy(Runnable asking) {
        int before = state.startConsulting();
        asking.run();
        return state.endConsulting(before);
    }

    private int answersAsked() {
        return askedBy(answers::contents);
    }

    private int countsAsked() {
        return askedBy(counts::contents);
    }

    private boolean same(ReadingState.Inputs then, int consulted) {
        return state.sameInputs(then, state.inputs(), false, consulted);
    }

    private static Ledger.OfEntries<String> holding(String... entries) {
        Ledger.OfEntries<String> out = new Ledger.OfEntries<>();
        for (String each : entries) {
            out.add(each);
        }
        return out;
    }

    @Test
    void aLedgerThatHoldsOtherEntriesIsAnotherInputToAReadingThatAskedWhatItHolds() {
        ReadingState.Inputs then;
        try (Restore _ = answers.set(holding("a"))) {
            then = state.inputs();
        }

        try (Restore _ = answers.set(holding("a", "b"))) {
            assertFalse(same(then, answersAsked()));
        }
    }

    @Test
    void thatThereIsALedgerIsAllAReadingThatDidNotAskWhatItHoldsDependsOn() {
        ReadingState.Inputs then;
        try (Restore _ = answers.set(holding("a"))) {
            then = state.inputs();
        }

        try (Restore _ = answers.set(holding("a", "b"))) {
            assertTrue(same(then, askedBy(answers::get)));
        }
    }

    @Test
    void aReadingThatDidNotAskAfterTheInputAtAllIsTakenWhateverItHoldsWhereThatIsTheRule() {
        ReadingState.Inputs then;
        try (Restore _ = answers.set(holding("a"))) {
            then = state.inputs();
        }

        assertTrue(state.sameAskedInputsBut(then, state.inputs(), 0, null));
        assertFalse(state.sameInputs(then, state.inputs(), false, 0),
                "the rule that compares every input compares this one");
    }

    @Test
    void anEntryGatheredUnderAKeyThatHoldsOneIsAnotherInputToAReadingThatAskedWhatItHolds() {
        Ledger.Grouped<String, String> gathered = new Ledger.Grouped<>();
        gathered.add("k", "a");
        try (Restore _ = counts.set(gathered)) {
            ReadingState.Inputs then = state.inputs();

            gathered.add("k", "b");

            assertFalse(same(then, countsAsked()));
            assertTrue(same(then, answersAsked()), "what another input holds is not asked");
        }
    }

    @Test
    void askingWhetherThereIsOneIsNotAskingWhatItHolds() {
        assertFalse(askedBy(answers::get) == answersAsked(),
                "reading what it holds asks after more than reading that there is one");
        assertTrue((askedBy(answers::get) & ~answersAsked()) == 0,
                "and after everything reading that there is one asks after");
    }
}
