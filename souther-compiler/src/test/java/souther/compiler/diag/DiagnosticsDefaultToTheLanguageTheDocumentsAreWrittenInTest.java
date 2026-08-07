package souther.compiler.diag;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.InputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;

import souther.compiler.Main;

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
 * happens to say does not answer half of the question. The one test that goes through the command
 * line runs it in a process of its own, with {@code SOUTHER_LANG} removed and the JVM locale set to
 * Japanese, which is the only way to see the whole path from a bare invocation to a printed banner
 * without the machine being part of the answer.
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

        String reported = compileInAProcessWithNoLanguageChosen(file);

        assertTrue(reported.contains("INVARIANT (WARNING)"), reported);
        assertTrue(reported.contains("may violate its invariant"), reported);
        assertFalse(reported.contains("警告"), reported);
    }

    /**
     * The pair to the one above: the Japanese catalog is still there and still reached, so what
     * changed is which language is answered when none was chosen, not whether the other one is
     * still spoken. In process, because an explicit {@code --lang} outranks the environment and
     * there is nothing left for the machine to decide.
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
    private static String compileInAProcessWithNoLanguageChosen(Path file) throws Exception {
        ProcessBuilder builder = new ProcessBuilder(
                Path.of(System.getProperty("java.home"), "bin", "java").toString(),
                "-Duser.language=ja", "-Duser.country=JP", "-Dfile.encoding=UTF-8",
                "-cp", System.getProperty("java.class.path"),
                Main.class.getName(),
                "compile", file.toString(),
                "-d", Files.createTempDirectory("souther-lang-out").toString());
        builder.environment().remove("SOUTHER_LANG");
        builder.redirectErrorStream(true);
        Process process = builder.start();
        String said;
        try (InputStream out = process.getInputStream()) {
            said = new String(out.readAllBytes(), StandardCharsets.UTF_8);
        }
        process.waitFor();
        return said;
    }

    /** What {@code souther compile} writes to stderr for {@code file}, in this process. */
    private static String compile(Path file, String... flags) throws Exception {
        List<String> args = new ArrayList<>(List.of("compile"));
        args.addAll(List.of(flags));
        args.add(file.toString());
        args.add("-d");
        args.add(Files.createTempDirectory("souther-lang-out").toString());
        PrintStream errWas = System.err;
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        System.setErr(new PrintStream(err, true, StandardCharsets.UTF_8));
        try {
            Main.main(args.toArray(new String[0]));
        } finally {
            System.setErr(errWas);
        }
        return err.toString(StandardCharsets.UTF_8);
    }

    private static Path write(String content) throws Exception {
        Path file = Files.createTempDirectory("souther-lang").resolve("probe.sou");
        Files.writeString(file, content);
        return file;
    }
}
