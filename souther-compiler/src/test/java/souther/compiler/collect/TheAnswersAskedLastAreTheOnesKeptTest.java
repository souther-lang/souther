package souther.compiler.collect;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A memo keeping the answers asked last keeps the ones asked most lately, however long ago they
 * were first worked out; lets the one asked longest ago go; and works out again, to what it was, an
 * answer it let go.
 */
class TheAnswersAskedLastAreTheOnesKeptTest {

    @Test
    void askingAgainKeepsAnAnswerAndTheOneAskedLongestAgoGoes() {
        LatelyAsked<String, String> answers = new LatelyAsked<>(2);
        List<String> worked = new ArrayList<>();

        assertEquals("A", answers.answer("a", q -> work(q, worked)));
        assertEquals("B", answers.answer("b", q -> work(q, worked)));
        // Asked again: "a" is now the one asked last, though it was worked out first.
        assertEquals("A", answers.answer("a", q -> work(q, worked)));
        // One more than it keeps: "b" was asked longest ago and goes, "a" stays.
        assertEquals("C", answers.answer("c", q -> work(q, worked)));
        assertEquals("A", answers.answer("a", q -> work(q, worked)), "kept");
        assertEquals("B", answers.answer("b", q -> work(q, worked)), "let go, worked out again");

        assertEquals(List.of("a", "b", "c", "b"), worked);
    }

    @Test
    void workingOutAnAnswerMayAskForAnother() {
        LatelyAsked<Integer, Integer> sums = new LatelyAsked<>(8);
        List<Integer> worked = new ArrayList<>();

        assertEquals(15, sumTo(5, sums, worked));
        assertEquals(21, sumTo(6, sums, worked));

        assertEquals(List.of(5, 4, 3, 2, 1, 0, 6), worked);
    }

    @Test
    void aQuestionAnsweredWithNothingIsRefused() {
        LatelyAsked<String, String> answers = new LatelyAsked<>(1);

        assertThrows(IllegalArgumentException.class, () -> answers.answer("a", _ -> null));
    }

    private static int sumTo(int n, LatelyAsked<Integer, Integer> sums, List<Integer> worked) {
        return sums.answer(n, asked -> {
            worked.add(asked);
            return asked == 0 ? 0 : asked + sumTo(asked - 1, sums, worked);
        });
    }

    private static String work(String asked, List<String> worked) {
        worked.add(asked);
        return asked.toUpperCase(Locale.ROOT);
    }
}
