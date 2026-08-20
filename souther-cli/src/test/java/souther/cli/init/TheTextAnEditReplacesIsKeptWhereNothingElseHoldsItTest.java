package souther.cli.init;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Locale;
import java.util.concurrent.TimeUnit;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A build file this command edits leaves its previous text beside it, unless something else is
 * already holding it.
 *
 * <p>Two answers rather than one, because a {@code .orig} beside a tracked and unmodified file is a
 * copy of what {@code git diff} says better, and it is the author who then deletes it. Which of the
 * two it is depends on the repository the file is in, so both are asked of a real one.
 */
class TheTextAnEditReplacesIsKeptWhereNothingElseHoldsItTest {

    private static final String POM = """
            <project>
              <groupId>com.acme</groupId>
              <artifactId>billing</artifactId>
            </project>
            """;

    @Test
    void aFileNoRepositoryHoldsGetsACopyBesideIt(@TempDir Path directory) throws IOException {
        Files.writeString(directory.resolve("pom.xml"), POM);

        String said = run(directory);

        assertEquals(POM, Files.readString(directory.resolve("pom.xml.orig")),
                "the author's own text was replaced and not kept anywhere");
        assertTrue(said.contains("pom.xml.orig"), "the copy is not reported:\n" + said);
    }

    /**
     * A file git is holding is edited without one.
     *
     * <p>Run against a real repository rather than a stand-in: what decides this is what {@code git}
     * answers about the file, and a test that asked something else would be asking a different
     * question from the one the command asks.
     */
    @Test
    void aTrackedAndUnmodifiedFileIsEditedWithoutACopy(@TempDir Path directory) throws Exception {
        git(directory, "init", "--quiet");
        Files.writeString(directory.resolve("pom.xml"), POM);
        git(directory, "add", "pom.xml");
        git(directory, "-c", "user.email=t@example.com", "-c", "user.name=T",
                "commit", "--quiet", "-m", "the pom");

        String said = run(directory);

        assertFalse(Files.exists(directory.resolve("pom.xml.orig")),
                "a copy was left beside a file git is already holding");
        assertFalse(said.contains(".orig"), said);
        assertFalse(POM.equals(Files.readString(directory.resolve("pom.xml"))),
                "nothing was edited, so this says nothing about the copy");
    }

    /** The same file, committed and then edited: what git holds is not what is about to be replaced. */
    @Test
    void aTrackedFileWithChangesInItGetsACopy(@TempDir Path directory) throws Exception {
        git(directory, "init", "--quiet");
        Files.writeString(directory.resolve("pom.xml"), POM);
        git(directory, "add", "pom.xml");
        git(directory, "-c", "user.email=t@example.com", "-c", "user.name=T",
                "commit", "--quiet", "-m", "the pom");
        String edited = POM.replace("</project>", "  <!-- mine -->\n</project>");
        Files.writeString(directory.resolve("pom.xml"), edited);

        run(directory);

        assertEquals(edited, Files.readString(directory.resolve("pom.xml.orig")),
                "the text that was there is not what was kept");
    }

    /** Runs the command in {@code here} and answers with what it wrote to stdout. */
    private static String run(Path here) {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        int code = InitCommand.run(new String[0], Locale.ENGLISH,
                new PrintStream(out, true, StandardCharsets.UTF_8),
                new PrintStream(err, true, StandardCharsets.UTF_8), here, "9.9.9");
        assertEquals(0, code, err.toString(StandardCharsets.UTF_8));
        return out.toString(StandardCharsets.UTF_8);
    }

    /**
     * Runs git in {@code directory}, and fails the test where it could not be run.
     *
     * <p>Not skipped where git is missing. What this covers is a decision the command makes by
     * asking git, and a run that quietly passed without one would report that the decision holds
     * having never reached it.
     */
    private static void git(Path directory, String... arguments) throws Exception {
        String[] line = new String[arguments.length + 1];
        line[0] = "git";
        System.arraycopy(arguments, 0, line, 1, arguments.length);
        Process process = new ProcessBuilder(line)
                .directory(directory.toFile())
                .redirectOutput(ProcessBuilder.Redirect.DISCARD)
                .redirectErrorStream(false)
                .start();
        assertTrue(process.waitFor(30, TimeUnit.SECONDS), "git did not finish: " + String.join(" ", line));
        assertEquals(0, process.exitValue(), "git failed: " + String.join(" ", line));
    }
}
