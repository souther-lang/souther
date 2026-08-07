package souther.compiler.diag;

import org.junit.jupiter.api.Test;

import souther.compiler.Main;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Everything the toolchain ships to read is written in English: the specification, the bundled
 * library topics, the CLI's own topics. A reader who chose no language is therefore answered in
 * English too, because that is the language the answer can be followed up in.
 *
 * <p>The machine's locale is not consulted. It says what language the operating system's own
 * interface is in, which is not evidence about which of the toolchain's languages this reader can
 * read — and taking it as evidence is what made the answer depend on the reader's machine rather
 * than on anything the toolchain decided.
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
    void theMachinesLocaleDoesNotChooseTheLanguage() {
        Locale was = Locale.getDefault();
        try {
            Locale.setDefault(Locale.JAPAN);

            assertEquals(Locale.ENGLISH, Messages.resolveLocale(null),
                    "a Japanese desktop is not a reader who can read the Japanese catalog");
        } finally {
            Locale.setDefault(was);
        }
    }

    @Test
    void aChosenLanguageIsStillTheOneAnswered() {
        assertEquals(Locale.JAPANESE, Messages.resolveLocale("ja"));
    }

    @Test
    void aCompileThatChoseNoLanguageIsAnsweredInEnglish() throws Exception {
        Locale was = Locale.getDefault();
        try {
            Locale.setDefault(Locale.JAPAN);
            Path file = write(UNPROVEN);

            String reported = compile(file);

            assertTrue(reported.contains("INVARIANT (WARNING)"), reported);
            assertTrue(reported.contains("may violate its invariant"), reported);
            assertFalse(reported.contains("警告"), reported);
        } finally {
            Locale.setDefault(was);
        }
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

    /** What {@code souther compile} writes to stderr for {@code file}. */
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
