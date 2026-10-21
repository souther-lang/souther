package souther.cli;

import souther.cli.CliProcess.Ran;
import souther.compiler.diag.Messages;
import org.junit.jupiter.api.Test;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.Map;


import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Everything the toolchain ships to be read is written in English: the specification, the bundled
 * library topics, the CLI's own topics. A reader who chose no language is therefore answered in
 * English too, because that is the language the answer can be followed up in.
 *
 * <p>The machine's locale is not consulted. It says which language the operating system's own
 * interface is in, which is not evidence about which of the toolchain's languages this reader can
 * read — and taking it as evidence is what made the answer depend on the reader's machine rather
 * than on anything the toolchain decided.
 *
 * <p>The precedence is asked about through the two-argument
 * {@link Messages#resolveLocale(String, String)}, so what the environment running these tests
 * happens to say does not answer half of the question. The tests that go through the command line
 * run it in an environment of their own, which names no language unless the test says so; the one
 * about a bare invocation also sets the JVM's locale to Japanese, so the whole path from a bare
 * invocation to a printed banner is seen without the machine being part of the answer.
 */
class DiagnosticsDefaultToTheLanguageTheDocumentsAreWrittenInTest {

    /** One unproven construction, on line 8. */
    private static final String UNPROVEN = """
            data Eaches = Int
                invariant value >= 0

            behavior wrap : (n: Int) -> Eaches
                constructs Eaches
            let wrap (n) = {
                let m = n
                Eaches(m)
            }
            """;

    @Test
    void nothingChosenAnywhereIsEnglish() {
        assertEquals(Locale.ENGLISH, Messages.resolveLocale(null, null));
    }

    @Test
    void theMachinesLocaleDoesNotChooseTheLanguage() {
        Locale was = Locale.getDefault();
        try {
            Locale.setDefault(Locale.JAPAN);

            assertEquals(Locale.ENGLISH, Messages.resolveLocale(null, null),
                    "a Japanese desktop is not a reader who can read the Japanese catalog");
        } finally {
            Locale.setDefault(was);
        }
    }

    @Test
    void theEnvironmentAnswersWhenNothingWasPassed() {
        assertEquals(Locale.JAPANESE, Messages.resolveLocale(null, "ja"));
    }

    @Test
    void whatWasPassedWinsOverTheEnvironment() {
        assertEquals(Locale.ENGLISH, Messages.resolveLocale("en", "ja"));
    }

    @Test
    void aBlankValueIsNotAChoice() {
        assertEquals(Locale.JAPANESE, Messages.resolveLocale("  ", "ja"),
                "an option given no value has not named a language");
        assertEquals(Locale.ENGLISH, Messages.resolveLocale(null, "  "));
    }

    @Test
    void aCompileThatChoseNoLanguageAnywhereIsAnsweredInEnglish() throws Exception {
        Path file = write(UNPROVEN);

        String reported = compileWithNoLanguageChosen(file);

        assertTrue(reported.contains("INVARIANT (WARNING)"), reported);
        assertTrue(reported.contains("may violate its invariant"), reported);
        assertFalse(reported.contains("警告"), reported);
    }

    /**
     * The pair to the one above: the Japanese catalog is still there and still reached, so what
     * changed is which language is answered when none was chosen, not whether the other one is
     * still spoken.
     */
    @Test
    void aCompileThatChoseJapaneseIsAnsweredInJapanese() throws Exception {
        Path file = write(UNPROVEN);

        String reported = compile(file, "--lang", "ja");

        assertTrue(reported.contains("(警告)"), reported);
        assertFalse(reported.contains("may violate its invariant"), reported);
    }

    /**
     * {@code souther compile} run with nothing that names a language: no {@code --lang}, no
     * {@code SOUTHER_LANG}, and a JVM whose own locale is Japanese. Both streams, since the point is
     * what a bare invocation prints.
     */
    private static String compileWithNoLanguageChosen(Path file) throws Exception {
        Locale was = Locale.getDefault();
        try {
            Locale.setDefault(Locale.JAPAN);
            Ran ran = compileRun(file);
            return ran.out() + ran.err();
        } finally {
            Locale.setDefault(was);
        }
    }

    /** What {@code souther compile} writes to stderr for {@code file}, in an empty environment. */
    private static String compile(Path file, String... flags) throws Exception {
        return compileRun(file, flags).err();
    }

    private static Ran compileRun(Path file, String... flags) throws Exception {
        Path scratch = Files.createTempDirectory("souther-lang-out");
        List<String> args = new ArrayList<>(List.of("compile"));
        args.addAll(List.of(flags));
        args.add(file.toString());
        args.add("-d");
        args.add(scratch.resolve("classes").toString());
        return CliInProcess.run(scratch, Map.of(), args.toArray(String[]::new));
    }

    private static Path write(String content) throws Exception {
        Path file = Files.createTempDirectory("souther-lang").resolve("probe.sou");
        Files.writeString(file, content);
        return file;
    }
}
