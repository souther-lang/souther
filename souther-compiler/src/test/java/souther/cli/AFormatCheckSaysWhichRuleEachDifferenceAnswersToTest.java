package souther.cli;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A gate that judged a file by computing its canonical form says which rule each difference answers
 * to.
 *
 * <p>It used to answer with the difference itself. A diff says which lines are not the canonical
 * form's and cannot say why any of them is there, so a reader who wanted to write the canonical form
 * rather than have it written for them had to work the rule out from the characters.
 *
 * <p>What is not named is said. A list that named what it can and stopped would read as a file with
 * these differences and no others, so the command shows a diff for whatever is left over — which
 * over every source measured is nothing.
 */
class AFormatCheckSaysWhichRuleEachDifferenceAnswersToTest {

    @TempDir
    Path dir;

    private record Said(int code, String err, String out) {}

    private Said run(String... args) {
        PrintStream originalErr = System.err;
        PrintStream originalOut = System.out;
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        System.setErr(new PrintStream(err, true, StandardCharsets.UTF_8));
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        try {
            int code = Main.dispatch(args);
            return new Said(code, err.toString(StandardCharsets.UTF_8),
                    out.toString(StandardCharsets.UTF_8));
        } finally {
            System.setErr(originalErr);
            System.setOut(originalOut);
        }
    }

    private Path source(String name, String text) throws Exception {
        Path file = dir.resolve(name);
        Files.writeString(file, text);
        return file;
    }

    private static final String UNFORMATTED = "module billing\n\ndata Note = {   body: String }\n";

    /** Each difference is a rule, a place in the reader's own source, and the two answers. */
    @Test
    void aFileThatIsNotFormattedIsAnsweredWithTheRulesItDiffersBy() throws Exception {
        Path file = source("m.sou", UNFORMATTED);

        Said said = run("fmt", file.toString(), "--check");

        assertEquals(1, said.code());
        assertTrue(said.out().contains(file + ":3:"),
                "the place is in the source the reader has: " + said.out());
        assertTrue(said.out().contains("writes its members one to a line"),
                "and the rule is named: " + said.out());
        assertTrue(said.out().contains("the canonical form:"), said.out());
    }

    /** A file already in its canonical form is answered with nothing. */
    @Test
    void aFileInItsCanonicalFormIsAnsweredWithNothing() throws Exception {
        Path file = source("m.sou", UNFORMATTED);
        String canonical = run("fmt", file.toString()).out();
        Path formatted = source("f.sou", canonical);

        Said said = run("fmt", formatted.toString(), "--check");

        assertEquals(0, said.code());
        assertEquals("", said.out());
    }

    /** A file that differs does not end the run: a reader who fixes only what the first line named
     * comes back for the next one on the next build. */
    @Test
    void everyFileThatDiffersIsShownAndNotOnlyTheFirst() throws Exception {
        Path first = source("first.sou", UNFORMATTED);
        Path second = source("second.sou", UNFORMATTED);

        Said said = run("fmt", first.toString(), second.toString(), "--check");

        assertEquals(1, said.code());
        assertTrue(said.out().contains(first + ":"), said.out());
        assertTrue(said.out().contains(second + ":"), said.out());
    }

    /**
     * A difference in the code tokens is a rule like any other.
     *
     * <p>A definition whose right-hand side is a lambda is written with its parameters on the left,
     * which writes tokens the source has not — so the rules that hold the two token streams side by
     * side have nothing to pair, and this used to be answered with a diff and the note that what was
     * named was not all of it. Which tokens are written is itself a decision, and it is the one the
     * others read.
     */
    @Test
    void aDifferenceInTheCodeTokensIsNamedTheSameWay() throws Exception {
        Path file = source("m.sou", """
                module billing exposing ( f )

                let f = (x) -> x
                """);

        Said said = run("fmt", file.toString(), "--check");

        assertEquals(1, said.code());
        assertTrue(said.out().contains("a definition writes its parameters to the left of the `=`"),
                "the rule is named: " + said.out());
        assertTrue(!said.out().contains("no rule accounts for yet"),
                "and there is nothing left over to show a diff for: " + said.out());
        assertTrue(!said.out().contains("@@"), said.out());
    }
}
