package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * An answer kept with what working it out asked is taken again by an asker given the same
 * answers, and by no other ({@link KeptByWhatItAsked}).
 */
class KeptByWhatItAskedTest {

    private final KeptByWhatItAsked<String, String, Integer> kept = new KeptByWhatItAsked<>();

    @Test
    void nothingIsKeptForWhatWasNotAsked() {
        assertNull(kept.of("a", _ -> true));
    }

    @Test
    void anAnswerIsTakenAgainWhereTheSameIsAnswered() {
        kept.keep("a", Map.of("p", true, "q", false), 1);

        assertEquals(1, kept.of("a", Set.of("p")::contains));
        assertEquals(1, kept.of("a", Set.of("p", "r")::contains),
                "what the work did not ask about is no part of what it turned on");
    }

    @Test
    void anAnswerIsNotTakenWhereAnythingItAskedIsAnsweredOtherwise() {
        kept.keep("a", Map.of("p", true, "q", false), 1);

        assertNull(kept.of("a", Set.of()::contains));
        assertNull(kept.of("a", Set.of("p", "q")::contains));
        assertNull(kept.of("b", Set.of("p")::contains));
    }

    @Test
    void theAnswerWorkedOutUnderEachSetOfAnswersIsKeptBesideTheOthers() {
        kept.keep("a", Map.of("p", true), 1);
        kept.keep("a", Map.of("p", false), 2);

        assertEquals(1, kept.of("a", Set.of("p")::contains));
        assertEquals(2, kept.of("a", Set.of()::contains));
    }

    @Test
    void workThatAskedNothingIsTakenByEveryAsker() {
        kept.keep("a", Map.of(), 1);

        assertEquals(1, kept.of("a", _ -> true));
        assertEquals(1, kept.of("a", _ -> false));
    }
}
