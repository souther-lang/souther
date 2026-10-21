package souther.cli;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import souther.cli.CliProcess.Ran;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
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
 * <p>In this JVM, with an environment that holds the variable and nothing else. The value a shell
 * exports reaches the command line as one entry of the environment {@link Main#main} reads once,
 * and from there the run is the same whether that environment was the process's or a test's.
 */
class TheLanguageAShellNamesIsHeldToTheSameTagsTest {

    @TempDir
    Path dir;

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

    /** Runs the command line with {@code environment} as the whole of its environment. */
    private Ran souther(Map<String, String> environment, String... args) {
        return CliInProcess.run(dir, environment, args);
    }

    /**
     * The reading this rests on. Without it a refusal would be indistinguishable from a variable
     * nothing ever looked at, and every case below would pass on a build that had stopped reading it.
     */
    @Test
    void theVariableNamesTheLanguageTheAnswerIsWrittenIn() throws Exception {
        Ran answer = souther(Map.of("SOUTHER_LANG", "ja"),
                "compile", source(BROKEN, "broken.sou").toString(), "-d", dir.resolve("out").toString());

        assertEquals(1, answer.code(), answer.err());
        assertTrue(answer.err().contains("構文エラー"), answer.err());
    }

    /**
     * A value that is not a tag is refused, naming where it was written. A reader sent to
     * {@code --lang} over a variable their shell exports is sent to fix something they did not
     * write.
     *
     * <p>A tag whose first subtag is a language and whose second says nothing, because that is the
     * one a tolerant reading would take for English. Whether a tag is one is
     * {@code ALanguageIsNamedByATagAndNotByACatalogTest}'s; what is asked here is what the command
     * line does with the answer when the shell gave the value.
     */
    @Test
    void aValueThatIsNotATagIsRefusedNamingTheVariableAndNotTheOption() throws Exception {
        Ran answer = souther(Map.of("SOUTHER_LANG", "en-!!"),
                "compile", source(MODEL, "ok.sou").toString(), "-d", dir.resolve("out").toString());

        assertEquals(2, answer.code(), answer.err());
        assertTrue(answer.err().contains("SOUTHER_LANG"), answer.err());
        assertTrue(answer.err().contains("en-!!"), answer.err());
        assertFalse(answer.err().contains("`--lang`"), answer.err());
        assertEquals("", answer.out(), answer.out());
    }

    /** A language with no catalog is named, here as on the line. */
    @Test
    void aLanguageThisCompilerHasNoCatalogForIsAccepted() throws Exception {
        Ran answer = souther(Map.of("SOUTHER_LANG", "fr"),
                "compile", source(MODEL, "ok.sou").toString(), "-d", dir.resolve("out").toString());

        assertEquals(0, answer.code(), answer.err());
    }

    /**
     * A variable exported empty is how a shell unsets one, and names no language. The line is not
     * read that way — the case below says so — so this is where the two part company.
     */
    @Test
    void aVariableExportedBlankIsAVariableNobodySet() throws Exception {
        Ran answer = souther(Map.of("SOUTHER_LANG", ""),
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
        Ran answer = souther(Map.of("SOUTHER_LANG", "ja"),
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
        Ran answer = souther(Map.of("SOUTHER_LANG", "!!"),
                "compile", source(BROKEN, "broken.sou").toString(), "-d", dir.resolve("out").toString(),
                "--lang", "ja");

        assertEquals(1, answer.code(), answer.err());
        assertTrue(answer.err().contains("構文エラー"), answer.err());
    }
}
