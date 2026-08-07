package souther.compiler;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A command that does not know an option says so, rather than opening it.
 *
 * <p>Each of these parsers ended with "anything I have no case for is a path", which is a decision
 * about a token taken without looking at it. An option written for another command, or misspelled,
 * became a file to read, and what the author heard back was about that file: {@code fmt} said
 * {@code io error: --lang: --lang}, and with nothing else on the line it counted the swallowed words
 * as files and asked for a flag the author had already written.
 */
class AnUnknownOptionIsNotAFileNameTest {

    @TempDir
    Path dir;

    private record Said(int code, String err, String out) {}

    /** Runs the command line and answers with its exit code and what it wrote. */
    private Said run(String... args) {
        PrintStream originalErr = System.err;
        PrintStream originalOut = System.out;
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        System.setErr(new PrintStream(err, true, StandardCharsets.UTF_8));
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        try {
            int code = Main.dispatch(args);
            return new Said(code, err.toString(StandardCharsets.UTF_8), out.toString(StandardCharsets.UTF_8));
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

    private static final String FORMATTED = """
            module billing

            data Note =
                { body: String
                }
            """;

    private static final String UNFORMATTED = "module billing\n\ndata Note = {   body: String }\n";

    @Test
    void fmtNamesAnOptionItDoesNotKnow() throws Exception {
        Said said = run("fmt", source("m.sou", FORMATTED).toString(), "--nope");

        assertEquals(2, said.code());
        assertTrue(said.err().contains("unknown option `--nope`"), said.err());
        assertFalse(said.err().contains("io error"), said.err());
    }

    @Test
    void compileNamesAnOptionItDoesNotKnow() throws Exception {
        Said said = run("compile", source("m.sou", FORMATTED).toString(), "--nope");

        assertEquals(2, said.code());
        assertTrue(said.err().contains("unknown option `--nope`"), said.err());
        assertFalse(said.err().contains("io error"), said.err());
    }

    @Test
    void examplesNamesAnOptionItDoesNotKnow() throws Exception {
        Said said = run("examples", source("m.sou", FORMATTED).toString(), "--nope");

        assertEquals(2, said.code());
        assertTrue(said.err().contains("unknown option `--nope`"), said.err());
        assertFalse(said.err().contains("io error"), said.err());
    }

    /**
     * The option exists; it is another command's. Saying which one is the difference between the
     * author fixing the line and the author looking for a file they never wrote.
     */
    @Test
    void fmtSaysWhichCommandsAnOptionOfTheirsBelongsTo() throws Exception {
        Said said = run("fmt", source("m.sou", FORMATTED).toString(), "--check", "--lang", "en");

        assertEquals(2, said.code());
        assertTrue(said.err().contains("unknown option `--lang`"), said.err());
        assertTrue(said.err().contains("compile/run/examples"), said.err());
    }

    /** The commands whose option it is still take it. */
    @Test
    void compileTakesTheSameOptionAsItsOwn() throws Exception {
        Said said = run("compile", source("m.sou", FORMATTED).toString(),
                "-d", dir.resolve("out").toString(), "--lang", "en");

        assertEquals(0, said.code());
        assertFalse(said.err().contains("unknown option"), said.err());
    }

    /** A file that reads as an option is not one: the check is on the token, before any path is built. */
    @Test
    void aSourceFileIsStillASourceFile() throws Exception {
        Said said = run("fmt", source("m.sou", FORMATTED).toString(), "--check");

        assertEquals(0, said.code());
        assertEquals("", said.err());
    }

    // --- what `--check` answers -----------------------------------------------------------------

    /**
     * The verdict is the exit code — a `--check` that cannot gate anything has no use. Pinned here
     * because a report doubted it, and because the answer travels through the value `dispatch` now
     * returns rather than through a call that ends the process.
     */
    @Test
    void checkFailsOnAFileThatIsNotFormatted() throws Exception {
        Path file = source("m.sou", UNFORMATTED);
        Said said = run("fmt", file.toString(), "--check");

        assertEquals(1, said.code());
        assertTrue(said.out().contains(file.toString()), said.out());
    }

    @Test
    void checkPassesOnAFileThatIsFormatted() throws Exception {
        Said said = run("fmt", source("m.sou", FORMATTED).toString(), "--check");

        assertEquals(0, said.code());
        assertEquals("", said.out());
    }

    /** A file it could not read is a failure of the run, whatever the formatted ones said. */
    @Test
    void checkFailsOnAFileItCannotRead() throws Exception {
        Said said = run("fmt", dir.resolve("absent.sou").toString(), "--check");

        assertEquals(1, said.code());
        assertTrue(said.err().contains("io error"), said.err());
    }
}
