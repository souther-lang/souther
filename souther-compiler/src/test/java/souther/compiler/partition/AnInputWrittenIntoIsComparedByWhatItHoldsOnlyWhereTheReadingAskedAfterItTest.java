package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An input a reading writes into stands as it did where it is there or is not, and, where the
 * reading asked what it holds, where it holds what it did ({@link ReadingState#sameInputsBut}).
 *
 * <p>Whether a list is there says nothing of what is in it, and a reading that goes through what
 * is in it ({@code isEmpty}, each element) depends on that: taken where another list is, with
 * the same being there, it would come to what the other list does not say. A map of lists is asked
 * what its lists hold too, and a copy of the map alone would not say that one of them was added
 * to.
 */
class AnInputWrittenIntoIsComparedByWhatItHoldsOnlyWhereTheReadingAskedAfterItTest {

    private static final class AnOwner {
        /** Read by the state through its role, and by nothing here but the test that sets it. */
        @SuppressWarnings("UnusedVariable")
        List<String> answers;
        /** Read by the state through its role, and by nothing here but the test that sets it. */
        @SuppressWarnings("UnusedVariable")
        Map<String, List<String>> counts;
        /** Set by a test that changes it, and read by the state through its role. */
        @SuppressWarnings("UnusedVariable")
        int another;
    }

    private static final Map<String, ReadingRole> ROLES = Map.of(
            "answers", ReadingRole.WRITTEN,
            "counts", ReadingRole.WRITTEN,
            "another", ReadingRole.INPUT);

    private final ReadingState state = new ReadingState(AnOwner.class, ROLES);
    private final AnOwner owner = new AnOwner();
    private final BitSet answersAsked = places("answers");
    private final BitSet countsAsked = places("counts");

    private BitSet places(String... names) {
        BitSet out = new BitSet();
        for (String name : names) {
            out.set(state.placeOfTheInput(name));
        }
        return out;
    }

    private boolean same(ReadingState.Inputs then, BitSet unconsulted, BitSet contentAsked) {
        return state.sameInputsBut(then, state.inputsOf(owner), false, unconsulted, contentAsked);
    }

    @Test
    void aListThatHoldsOtherElementsIsAnotherInputToAReadingThatAskedWhatItHolds() {
        owner.answers = new ArrayList<>(List.of("a"));
        ReadingState.Inputs then = state.inputsOf(owner);

        owner.answers = new ArrayList<>(List.of("a", "b"));

        assertFalse(same(then, null, answersAsked));
    }

    @Test
    void thatThereIsAListIsAllAReadingThatDidNotAskWhatItHoldsDependsOn() {
        owner.answers = new ArrayList<>(List.of("a"));
        ReadingState.Inputs then = state.inputsOf(owner);

        owner.answers = new ArrayList<>(List.of("a", "b"));

        assertTrue(same(then, null, null));
    }

    @Test
    void aReadingThatDidNotAskAfterTheInputAtAllIsTakenWhateverItHolds() {
        owner.answers = new ArrayList<>(List.of("a"));
        ReadingState.Inputs then = state.inputsOf(owner);

        owner.answers = null;

        assertTrue(same(then, places("answers"), null));
    }

    @Test
    void aListThatIsThereIsNotAListThatIsNotWhateverTheReadingAskedOfIt() {
        owner.answers = null;
        ReadingState.Inputs then = state.inputsOf(owner);

        owner.answers = new ArrayList<>();

        assertFalse(same(then, null, null));
        assertFalse(same(then, null, answersAsked));
    }

    @Test
    void theSameElementsAreTheSameInputWhereWhatItHoldsIsAsked() {
        String element = "a";
        owner.answers = new ArrayList<>(List.of(element));
        ReadingState.Inputs then = state.inputsOf(owner);

        owner.answers = new ArrayList<>(List.of(element));

        assertTrue(same(then, null, answersAsked));
    }

    @Test
    void aListAddedToInsideAMapIsAnotherInputToAReadingThatAskedWhatTheMapHolds() {
        List<String> inner = new ArrayList<>(List.of("a"));
        owner.counts = new LinkedHashMap<>(Map.of("k", inner));
        ReadingState.Inputs then = state.inputsOf(owner);

        inner.add("b");

        assertFalse(same(then, null, countsAsked));
        assertTrue(same(then, null, answersAsked), "what another input holds is not asked");
    }

    @Test
    void whatAnotherInputHoldsIsNotComparedForAnInputThatIsNotWrittenInto() {
        owner.answers = new ArrayList<>(List.of("a"));
        ReadingState.Inputs then = state.inputsOf(owner);

        owner.another = 1;

        assertFalse(same(then, null, answersAsked));
    }
}
