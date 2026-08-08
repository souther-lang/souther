package souther.compiler;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import souther.compiler.report.UnifiedDiff;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A gate that judged a file by computing its canonical form says what it compared.
 *
 * <p>The verdict alone was a file name and an exit code, which left the reader to obtain the other
 * text themselves — by writing the file over with {@code -w} and diffing it against a copy, or by
 * running the formatter a second time into a scratch file. Both texts are in hand at the moment the
 * verdict is taken, so the difference goes out then, and the canonical form is never carried past
 * the file it was computed for.
 *
 * <p>Under the difference, the rule each spacing departure breaks. The difference says what the
 * canonical form would write and that says which rule says so, which is what the reader asks next.
 */
class AFormatCheckShowsTheDifferenceItDecidedOnTest {

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

    /** What the gate shows is the canonical form it judged against, and not another reading of the
     * file: the same text {@code fmt} prints when asked for it. */
    @Test
    void aFileThatIsNotFormattedIsAnsweredWithTheDifferenceItDecidedOn() throws Exception {
        Path file = source("m.sou", UNFORMATTED);
        String canonical = run("fmt", file.toString()).out();
        assertNotEquals(UNFORMATTED, canonical);

        Said said = run("fmt", file.toString(), "--check");

        assertEquals(1, said.code());
        assertTrue(said.out().startsWith(
                UnifiedDiff.of(file.toString(), file + " (formatted)", UNFORMATTED, canonical)),
                said.out());
        assertTrue(said.out().contains("@@"), said.out());
    }

    /** And under it, the rule the file departs from, where the departure is a spacing one. */
    @Test
    void andTheRuleEachSpacingDepartureBreaks() throws Exception {
        Path file = source("m.sou", UNFORMATTED);

        Said said = run("fmt", file.toString(), "--check");

        assertEquals(List.of(file + ":3:14: LBRACE IDENT under PRODUCT_BODY:"
                        + " this writes [   ] and the canonical form writes [ ]"),
                said.out().lines().filter(line -> line.startsWith(file.toString())).toList());
    }

    /** The name the verdict used to be is in the header the difference already carries. Said twice,
     * a reader scanning a CI log counts a file that differs as two. */
    @Test
    void theNameIsNotSaidApartFromTheDifferenceItHeads() throws Exception {
        Path file = source("m.sou", UNFORMATTED);

        Said said = run("fmt", file.toString(), "--check");

        assertEquals("--- " + file, said.out().lines().findFirst().orElseThrow());
        assertEquals(0, said.out().lines().filter(line -> line.equals(file.toString())).count(),
                said.out());
    }

    /** A file that differs does not end the run: a reader who fixes only what the first line named
     * comes back for the next one on the next build. */
    @Test
    void everyFileThatDiffersIsShownAndNotOnlyTheFirst() throws Exception {
        Path first = source("first.sou", UNFORMATTED);
        Path second = source("second.sou", UNFORMATTED);

        Said said = run("fmt", first.toString(), second.toString(), "--check");

        assertEquals(1, said.code());
        assertTrue(said.out().contains("--- " + first), said.out());
        assertTrue(said.out().contains("--- " + second), said.out());
    }
}
