package souther.compiler.diag;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A diagnostic is answered in a language somebody chose, or in the one Souther defaults to. It is
 * never answered in a language read off the machine.
 *
 * <p>The machine's locale says which language the operating system's own interface is in. For a
 * toolchain whose documents are written in one language that cannot be evidence about the reader:
 * most values of it select an answer with nothing behind it to read, and taking it as evidence made
 * the language of a report depend on where the compiler ran rather than on anything anybody
 * decided. It was read once, and every entry point added since had the same reading available to
 * it.
 *
 * <p>What holds today is that the default is English and the only environment consulted is
 * {@code SOUTHER_LANG}, read in one place. Nothing was holding it: the test next door asks
 * {@link Messages#resolveLocale} what it answers, which a new adapter resolving a locale of its own
 * never goes through.
 *
 * <p>This is a tripwire and not a proof. It reads the sources for the ways the machine's language
 * is asked for, and a static import or a helper in between defeats it. What makes the property
 * structurally true is one owner for the choice, which the adapters do not have yet — each decides
 * for itself which language it renders in, and that is tracked on its own. Until then, the reading
 * that would have to be added first is the one this fails on.
 */
class TheDiagnosticLanguageIsNeverDerivedFromTheMachineTest {

    /**
     * The ways a process is told what language its machine is in: the JVM's answer, the property
     * behind it, and the environment Unix states it in — {@code LC_MESSAGES} most directly of the
     * three, being the one that names the language of messages specifically.
     */
    private static final List<String> AMBIENT = List.of(
            "Locale.getDefault(",
            "\"user.language\"",
            "\"LANG\"",
            "\"LC_ALL\"",
            "\"LC_MESSAGES\"");

    @Test
    void diagnosticLanguageIsNeverDerivedFromTheMachineLocale() throws IOException {
        List<Path> sources = EveryShippedMessageCatalogIsCompleteAndValidTest.mainSources();
        assertFalse(sources.isEmpty(), "found no sources at all — the scan missed the tree");

        Set<String> reading = new TreeSet<>();
        for (Path source : sources) {
            String text = Files.readString(source, StandardCharsets.UTF_8);
            for (String ambient : AMBIENT) {
                if (text.contains(ambient)) {
                    reading.add(source.toString().replace('\\', '/')
                            .replaceAll(".*/src/main/java/", "") + " reads " + ambient);
                }
            }
        }
        assertEquals(Set.of(), reading,
                "the machine's language is being read; a diagnostic is answered in a language that"
                        + " was named — through `--lang`, `SOUTHER_LANG` or an adapter's own"
                        + " option — or in Messages.defaultLocale()");
    }
}
