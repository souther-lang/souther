package souther.compiler.collect;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * An answer asked for again while it is kept is not worked out again; a question whose hash falls
 * in the slot of another is answered for itself and never with the other's answer; and an answer
 * no longer kept is worked out again to what it was.
 */
class AnAnswerKeptIsNotWorkedOutAgainTest {

    /** A question whose hash is chosen, so that two unequal ones fall in one slot. */
    private record Asked(String name, int hash) {
        @Override
        public int hashCode() {
            return hash;
        }
    }

    @Test
    void anAnswerKeptIsHandedBackAndOneDisplacedIsWorkedOutAgain() {
        RecentAnswers<Asked, String> answers = new RecentAnswers<>(4);
        List<String> worked = new ArrayList<>();
        Asked a = new Asked("a", 3);
        Asked b = new Asked("b", 3);

        assertEquals("A", answers.answer(a, q -> work(q, worked)));
        assertEquals("A", answers.answer(new Asked("a", 3), q -> work(q, worked)));
        assertEquals("B", answers.answer(b, q -> work(q, worked)), "another question in the slot");
        assertEquals("A", answers.answer(a, q -> work(q, worked)), "displaced, worked out again");

        assertEquals(List.of("a", "b", "a"), worked);
    }

    private static String work(Asked asked, List<String> worked) {
        worked.add(asked.name());
        return asked.name().toUpperCase(Locale.ROOT);
    }
}
