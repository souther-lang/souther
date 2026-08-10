package souther.compiler;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code SOUTHER_LANG} names a language the way {@code --lang} does, and is held to the same tags.
 *
 * <p>A variable is not ambient information about the machine — that is what {@code LANG} is, and it
 * is never read. Something set this one for Souther, so a value it cannot read is somebody trying to
 * name a language and failing, which is the case an answer in English hides: nothing named a
 * language and something named one that says nothing come back identical.
 *
 * <p>In a process of its own, because the environment is what is being varied and a test cannot set
 * one for the JVM it is running in. This is also the only reading of it that goes through everything
 * a shell's value passes on the way in.
 */
class TheLanguageAShellNamesIsHeldToTheSameTagsTest {

    @TempDir
    Path dir;

    private record Answer(int code, String out, String err) {}

    private static final String MODEL = """
            module example.ok

            data Celsius = Int
            """;

    /** A source with a mistake in it, so that which language the answer is written in is visible. */
    private static final String BROKEN = """
            module example.broken

            data Foo = Foo { bar : Nope }
            """;

    private Path source(String text, String name) throws IOException {
        Path file = dir.resolve(name);
        Files.writeString(file, text);
        return file;
    }

    /**
     * Runs the command line in a process whose environment is the one named here.
     *
     * <p>Through {@code Main} on this test's own class path rather than through the shipped jar,
     * which is built a module later. What is being read is the environment, and it arrives the same
     * way either side of the packaging.
     */
    private Answer souther(Map<String, String> environment, String... args)
            throws IOException, InterruptedException {
        List<String> command = new java.util.ArrayList<>(List.of(
                Path.of(System.getProperty("java.home"), "bin", "java").toString(),
                "-cp", System.getProperty("java.class.path"),
                Main.class.getName()));
        command.addAll(List.of(args));
        ProcessBuilder builder = new ProcessBuilder(command);
        builder.environment().putAll(environment);
        Process process = builder.start();
        String out = new String(process.getInputStream().readAllBytes(), StandardCharsets.UTF_8);
        String err = new String(process.getErrorStream().readAllBytes(), StandardCharsets.UTF_8);
        return new Answer(process.waitFor(), out, err);
    }

    /**
     * The reading this rests on. Without it a refusal would be indistinguishable from a variable
     * nothing ever looked at, and every case below would pass on a build that had stopped reading it.
     */
    @Test
    void theVariableNamesTheLanguageTheAnswerIsWrittenIn() throws Exception {
        Answer answer = souther(Map.of("SOUTHER_LANG", "ja"),
                "compile", source(BROKEN, "broken.sou").toString(), "-d", dir.resolve("out").toString());

        assertEquals(1, answer.code(), answer.err());
        assertTrue(answer.err().contains("構文エラー"), answer.err());
    }

    @Test
    void aValueThatIsNotATagIsRefused() throws Exception {
        Answer answer = souther(Map.of("SOUTHER_LANG", "en-!!"),
                "compile", source(MODEL, "ok.sou").toString(), "-d", dir.resolve("out").toString());

        assertEquals(2, answer.code(), answer.err());
        assertTrue(answer.err().contains("SOUTHER_LANG"), answer.err());
        assertTrue(answer.err().contains("en-!!"), answer.err());
        assertEquals("", answer.out(), answer.out());
    }

    /** Naming where it was written. A reader sent to `--lang` over a variable their shell exports is
     *  sent to fix something they did not write. */
    @Test
    void theRefusalNamesTheVariableAndNotTheOption() throws Exception {
        Answer answer = souther(Map.of("SOUTHER_LANG", "!!"),
                "compile", source(MODEL, "ok.sou").toString(), "-d", dir.resolve("out").toString());

        assertEquals(2, answer.code(), answer.err());
        assertFalse(answer.err().contains("`--lang`"), answer.err());
    }

    /** A language with no catalog is named, here as on the line. */
    @Test
    void aLanguageThisCompilerHasNoCatalogForIsAccepted() throws Exception {
        Answer answer = souther(Map.of("SOUTHER_LANG", "fr"),
                "compile", source(MODEL, "ok.sou").toString(), "-d", dir.resolve("out").toString());

        assertEquals(0, answer.code(), answer.err());
    }

    /**
     * A variable exported empty is how a shell unsets one, and names no language. The line is not
     * read that way — the case below says so — so this is where the two part company.
     */
    @Test
    void aVariableExportedBlankIsAVariableNobodySet() throws Exception {
        Answer answer = souther(Map.of("SOUTHER_LANG", ""),
                "compile", source(MODEL, "ok.sou").toString(), "-d", dir.resolve("out").toString());

        assertEquals(0, answer.code(), answer.err());
    }

    /**
     * And a line writing the option with nothing in it is not a line that left it out. It named a
     * language and named it badly; falling back to the variable would answer it in a language it did
     * not ask for, which is what this did.
     */
    @Test
    void aBlankValueOnTheLineDoesNotFallBackToTheVariable() throws Exception {
        Answer answer = souther(Map.of("SOUTHER_LANG", "ja"),
                "compile", source(BROKEN, "broken.sou").toString(), "-d", dir.resolve("out").toString(),
                "--lang", "");

        assertEquals(2, answer.code(), answer.err());
        assertTrue(answer.err().contains("`--lang`"), answer.err());
        assertFalse(answer.err().contains("構文エラー"),
                "the compile did not run: " + answer.err());
        assertFalse(answer.err().contains("整形式の言語タグ"),
                "and the refusal is not written in the language the line outranked: " + answer.err());
    }

    /**
     * And the value that lost the precedence is not read at all. The line names the language, so a
     * variable that names nothing is not what this invocation was going to be answered in — holding
     * it to being a tag would leave a reader whose shell exports something malformed unable to name
     * a language from the line either.
     */
    @Test
    void aLineThatNamesALanguageIsNotRefusedForWhatTheShellSet() throws Exception {
        Answer answer = souther(Map.of("SOUTHER_LANG", "!!"),
                "compile", source(BROKEN, "broken.sou").toString(), "-d", dir.resolve("out").toString(),
                "--lang", "ja");

        assertEquals(1, answer.code(), answer.err());
        assertTrue(answer.err().contains("構文エラー"), answer.err());
    }
}
