package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.ReadingState.Compared;
import souther.compiler.partition.ReadingState.Restore;
import souther.compiler.partition.ReadingState.Scoped;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An input a reading writes into stands as it did where it is there or is not, and, where the
 * reading asked what it holds, where it holds what it did ({@link ReadingState#sameInputs}).
 *
 * <p>Whether a list is there says nothing of what is in it, and a reading that goes through what
 * is in it ({@code isEmpty}, each element) depends on that: taken where another list is, with
 * the same being there, it would come to what the other list does not say. A map of lists is asked
 * what its lists hold too, and a copy of the map alone would not say that one of them was added
 * to.
 */
class AnInputWrittenIntoIsComparedByWhatItHoldsOnlyWhereTheReadingAskedAfterItTest {

    private final ReadingState state = new ReadingState();
    private final Scoped<List<String>> answers = state.writtenIntoAndAskedAfter();
    private final Scoped<Map<String, List<String>>> counts = state.writtenIntoAndAskedAfter();
    private final Scoped<Integer> another = state.setting(Compared.BY_VALUE, 0);

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

    @Test
    void aListThatHoldsOtherElementsIsAnotherInputToAReadingThatAskedWhatItHolds() {
        ReadingState.Inputs then;
        try (Restore _ = answers.set(new ArrayList<>(List.of("a")))) {
            then = state.inputs();
        }

        try (Restore _ = answers.set(new ArrayList<>(List.of("a", "b")))) {
            assertFalse(same(then, answersAsked()));
        }
    }

    @Test
    void thatThereIsAListIsAllAReadingThatDidNotAskWhatItHoldsDependsOn() {
        ReadingState.Inputs then;
        try (Restore _ = answers.set(new ArrayList<>(List.of("a")))) {
            then = state.inputs();
        }

        try (Restore _ = answers.set(new ArrayList<>(List.of("a", "b")))) {
            assertTrue(same(then, askedBy(answers::get)));
        }
    }

    @Test
    void aReadingThatDidNotAskAfterTheInputAtAllIsTakenWhateverItHoldsWhereThatIsTheRule() {
        ReadingState.Inputs then;
        try (Restore _ = answers.set(new ArrayList<>(List.of("a")))) {
            then = state.inputs();
        }

        assertTrue(state.sameAskedInputsBut(then, state.inputs(), 0, null));
        assertFalse(state.sameInputs(then, state.inputs(), false, 0),
                "the rule that compares every input compares this one");
    }

    @Test
    void aListThatIsThereIsNotAListThatIsNotWhateverTheReadingAskedOfIt() {
        ReadingState.Inputs then = state.inputs();

        try (Restore _ = answers.set(new ArrayList<>())) {
            assertFalse(same(then, 0));
            assertFalse(same(then, answersAsked()));
        }
    }

    @Test
    void theSameElementsAreTheSameInputWhereWhatItHoldsIsAsked() {
        String element = "a";
        ReadingState.Inputs then;
        try (Restore _ = answers.set(new ArrayList<>(List.of(element)))) {
            then = state.inputs();
        }

        try (Restore _ = answers.set(new ArrayList<>(List.of(element)))) {
            assertTrue(same(then, answersAsked()));
        }
    }

    @Test
    void aListAddedToInsideAMapIsAnotherInputToAReadingThatAskedWhatTheMapHolds() {
        List<String> inner = new ArrayList<>(List.of("a"));
        try (Restore _ = counts.set(new LinkedHashMap<>(Map.of("k", inner)))) {
            ReadingState.Inputs then = state.inputs();

            inner.add("b");

            assertFalse(same(then, countsAsked()));
            assertTrue(same(then, answersAsked()), "what another input holds is not asked");
        }
    }

    @Test
    void whatAnotherInputHoldsIsNotComparedForAnInputThatIsNotWrittenInto() {
        ReadingState.Inputs then;
        try (Restore _ = answers.set(new ArrayList<>(List.of("a")))) {
            then = state.inputs();
            try (Restore _ = another.set(1)) {
                assertFalse(same(then, answersAsked()));
            }
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
