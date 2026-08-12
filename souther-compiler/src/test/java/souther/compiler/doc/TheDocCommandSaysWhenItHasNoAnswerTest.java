package souther.compiler.doc;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Silence is the one answer a lookup tool may not give: a reader who gets nothing back cannot tell
 * a term that is absent from a tool that is broken, and stops trusting it either way.
 */
class TheDocCommandSaysWhenItHasNoAnswerTest {

    private record Answer(int code, String out, String err) {}

    private Answer run(String... args) {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        int code = DocCommand.run(args,
                new PrintStream(out, true, StandardCharsets.UTF_8),
                new PrintStream(err, true, StandardCharsets.UTF_8));
        return new Answer(code, out.toString(StandardCharsets.UTF_8), err.toString(StandardCharsets.UTF_8));
    }

    @Test
    void aSearchThatMatchesNothingSaysSoRatherThanPrintingNothing() {
        Answer answer = run("--search", "borrowck");

        assertTrue(answer.err().contains("nothing says `borrowck`"), "it says the term drew a blank: " + answer.err());
        assertEquals("", answer.out(), "and does not leave the reader reading an empty stdout");
    }

    @Test
    void aSearchOfSeveralWordsFallsBackToTheWordsWhenThePhraseIsAbsent() {
        Answer answer = run("--search", "optional field null");

        assertEquals(0, answer.code());
        assertTrue(answer.out().lines().count() > 0,
                "the words are searched when the phrase itself is nowhere:\n" + answer.err());
        assertTrue(answer.err().contains("no section says `optional field null`"),
                "and it is said that the phrase itself was not found: " + answer.err());
    }

    @Test
    void aSecondAnchorIsNotSilentlyDiscarded() {
        Answer answer = run("purpose", "newtype");

        assertTrue(answer.err().contains("one at a time"),
                "asking for two sections is answered, not half-ignored: " + answer.err());
    }
}
