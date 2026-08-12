package souther.cli;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import tools.jackson.databind.json.JsonMapper;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;

/**
 * A warning says the run-time check stands, which is a fact about the construction and not about
 * whether the build should go on. Those are two questions, and only the first one was being asked:
 * a compile that warned wrote its classes and exited 0, so a project that wanted the warnings gone
 * had no way to hold itself to it and they accumulated while the build stayed green.
 *
 * <p>The answer is an acceptance rule and not a severity: {@code --warnings error} decides whether a
 * compile carrying warnings is accepted, and the diagnostics it prints are the same warnings they
 * were. Rewriting them to errors would say the construction is refused, which is not what the check
 * found.
 */
class ABuildThatWarnsCanBeRefusedTest {

    @TempDir
    Path dir;

    /** One unproven construction: nothing is known of the Int the name was given. */
    private static final String WARNS = """
            module m

            data Eaches = Int
                invariant value >= 0

            behavior wrap : (n: Int) -> Eaches
                constructs Eaches
            let wrap (n) = {
                let m = n
                Eaches(m)
            }
            """;

    private static final String CLEAN = """
            module m

            data Note = { body: String }
            """;

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

    private Path source(String text) throws Exception {
        Path file = dir.resolve("m.sou");
        Files.writeString(file, text);
        return file;
    }

    private Path outDir() {
        return dir.resolve("out");
    }

    private List<Path> written() throws Exception {
        if (!Files.isDirectory(outDir())) {
            return List.of();
        }
        try (var walk = Files.walk(outDir())) {
            return walk.filter(Files::isRegularFile).toList();
        }
    }

    // --- what the rule decides ------------------------------------------------------------------

    @Test
    void aCompileThatWarnsIsRefusedWhenWarningsAreErrors() throws Exception {
        Said said = run("compile", source(WARNS).toString(), "-d", outDir().toString(),
                "--warnings", "error", "--lang", "en");

        assertEquals(1, said.code(), said.err());
    }

    @Test
    void aCompileThatWarnsIsAcceptedWhenTheyAreOnlyReported() throws Exception {
        Said said = run("compile", source(WARNS).toString(), "-d", outDir().toString(),
                "--warnings", "report", "--lang", "en");

        assertEquals(0, said.code(), said.err());
        assertTrue(said.err().contains("E2011"), "the warning is still reported: " + said.err());
    }

    /** The default is what the command did before there was an option to write. */
    @Test
    void reportingIsWhatAnUnaskedCompileDoes() throws Exception {
        Said said = run("compile", source(WARNS).toString(), "-d", outDir().toString(),
                "--lang", "en");

        assertEquals(0, said.code(), said.err());
        assertTrue(said.err().contains("E2011"), said.err());
    }

    @Test
    void aCompileThatDoesNotWarnIsAcceptedWhenWarningsAreErrors() throws Exception {
        Said said = run("compile", source(CLEAN).toString(), "-d", outDir().toString(),
                "--warnings", "error", "--lang", "en");

        assertEquals(0, said.code(), said.err());
        assertFalse(written().isEmpty(), "a clean compile still writes its classes");
    }

    /**
     * A refused build writes no classes. The exit code says the build was not accepted, and classes
     * this run had written are what a later step would pick up as the output of one that was.
     *
     * <p>What it does not say is that the output directory is empty afterwards: classes an earlier
     * run left there stay, as they do when a compile fails. Removing those is a separate question
     * about who owns that directory, and the same one for both.
     */
    @Test
    void aRefusedCompileWritesNoClasses() throws Exception {
        run("compile", source(WARNS).toString(), "-d", outDir().toString(),
                "--warnings", "error", "--lang", "en");

        assertEquals(List.of(), written(), "the refused build wrote classes");
    }

    // --- what it prints -------------------------------------------------------------------------

    /** The diagnostic is about the construction; the rule is about the build. Only the second one
     * changed, so the first says what it said. */
    @Test
    void theDiagnosticIsStillAWarning() throws Exception {
        Said said = run("compile", source(WARNS).toString(), "-d", outDir().toString(),
                "--warnings", "error", "--lang", "en");

        assertTrue(said.err().contains("INVARIANT (WARNING)"), said.err());
        assertTrue(said.err().contains("E2011"), said.err());
        assertFalse(said.err().contains("INVARIANT  E2011"),
                "the warning was not re-titled as an error: " + said.err());
    }

    @Test
    void theRefusalSaysWhyTheBuildStopped() throws Exception {
        Said said = run("compile", source(WARNS).toString(), "-d", outDir().toString(),
                "--warnings", "error", "--lang", "en");

        assertTrue(said.err().contains("warnings are treated as errors"),
                "an exit code alone does not say which flag decided it: " + said.err());
    }

    @Test
    void theRefusalFollowsTheChosenLanguage() throws Exception {
        Said said = run("compile", source(WARNS).toString(), "-d", outDir().toString(),
                "--warnings", "error", "--lang", "ja");

        assertTrue(said.err().contains("警告"), said.err());
        assertFalse(said.err().contains("warnings are treated as errors"), said.err());
    }

    /**
     * The JSON renderer writes one object per diagnostic and no envelope around them, so what a tool
     * reads is JSON lines. A sentence appended there is a line that does not parse, and the reader
     * that was given it has no way to skip what it cannot name. Under this format the exit code is
     * what says the build was refused.
     */
    @Test
    void underJsonEveryLineIsStillOneDiagnostic() throws Exception {
        Said said = run("compile", source(WARNS).toString(), "-d", outDir().toString(),
                "--warnings", "error", "--format", "json", "--lang", "en");

        assertEquals(1, said.code(), said.err());
        JsonMapper json = JsonMapper.builder().build();
        for (String line : said.err().split("\\R")) {
            if (line.isBlank()) {
                continue;
            }
            assertDoesNotThrow(() -> json.readTree(line), "not a JSON line: " + line);
        }
        assertTrue(said.err().contains("\"severity\":\"warning\""), said.err());
    }

    // --- what the option accepts ----------------------------------------------------------------

    @Test
    void warningsTakesReportOrError() throws Exception {
        Said said = run("compile", source(WARNS).toString(), "-d", outDir().toString(),
                "--warnings", "nope");

        assertEquals(2, said.code(), said.err());
        assertTrue(said.err().contains("`--warnings` takes report or error"), said.err());
    }

    @Test
    void warningsNeedsAValue() throws Exception {
        Said said = run("compile", source(WARNS).toString(), "-d", outDir().toString(),
                "--warnings");

        assertEquals(2, said.code(), said.err());
    }
}
