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
 * A diagnostic is rendered in a language, and every place that picks one is listed here.
 *
 * <p>The list is short because most of the tree never picks: a renderer is handed the language and a
 * pass reporting a problem does not know there is one. What picks is a surface that answers a
 * reader — it has to say which reader — and the one operation whose text is not for a reader at all.
 *
 * <p>Each surface picks once. Picking twice is how a surface stops having a policy: the second site
 * is written to match the first and then only one of them is revisited. The LSP had two, and the
 * CLI had three of one resolution.
 *
 * <p>What is deliberately not here is a table in the diagnostics layer naming the surfaces. That
 * would make the layer know every adapter, and an adapter's language comes from the adapter's own
 * option — the CLI's flag, the processor's option, the editor telling a language server nothing.
 * The layer offers the resolution; naming which surface uses it is the surface's own line. This test
 * is where they are enumerated, so a new one is a line here rather than a fact nobody wrote down.
 *
 * <p>A tripwire and not a proof, like the machine-locale test next door: it reads the sources, and a
 * helper in between defeats it. What it does hold is the reading that would have to be added first.
 */
class EverySurfaceThatAnswersAReaderNamesItsLanguageTest {

    /** The ways a source picks a language for a diagnostic. {@code Locale.ROOT} is not one of them:
     *  it is case folding, which is about the bytes and not about a reader. */
    private static final List<String> PICKING = List.of(
            "Messages.resolveLocale(",
            "Messages.defaultLocale()",
            "Locale.ENGLISH",
            "Locale.JAPANESE",
            "Locale.JAPAN",
            "Locale.forLanguageTag(",
            "Locale.of(");

    /** The resolution itself lives here, so this file names languages as its subject matter. */
    private static final String RESOLVER = "souther/compiler/diag/Messages.java";

    /**
     * Every pick in the tree.
     *
     * <p>Three surfaces answer a reader. The CLI and the annotation processor resolve, from the flag
     * and from the processor option; a language server is not told the editor's UI locale, so there
     * is nothing for it to resolve from and it names English outright.
     *
     * <p>The fourth is not a surface. It is the one-line text a {@code CompileException} carries for
     * {@code getMessage()}, which no adapter prints while the exception carries a diagnostic — and
     * the two sites that build it always supply one. It has no reader whose language could be
     * asked, so the language is written where the text is made and no caller can pass one.
     */
    private static final Set<String> NAMED = Set.of(
            "souther/compiler/Main.java picks Messages.resolveLocale(",
            "souther/compiler/apt/SoutherProcessor.java picks Messages.resolveLocale(",
            "souther/lsp/analysis/Analyzer.java picks Locale.ENGLISH",
            "souther/compiler/diag/DiagnosticRenderer.java picks Locale.ENGLISH");

    @Test
    void everyPickOfADiagnosticLanguageIsOneOfTheNamedOnes() throws IOException {
        List<Path> sources = EveryShippedMessageCatalogIsCompleteAndValidTest.mainSources();
        assertFalse(sources.isEmpty(), "found no sources at all — the scan missed the tree");

        Set<String> picks = new TreeSet<>();
        for (Path source : sources) {
            String path = source.toString().replace('\\', '/').replaceAll(".*/src/main/java/", "");
            if (path.equals(RESOLVER)) {
                continue;
            }
            String text = Files.readString(source, StandardCharsets.UTF_8);
            for (String picking : PICKING) {
                int count = occurrences(text, picking);
                if (count > 0) {
                    picks.add(path + " picks " + picking
                            + (count == 1 ? "" : " (" + count + " times)"));
                }
            }
        }

        assertEquals(new TreeSet<>(NAMED), picks,
                "a diagnostic's language is picked somewhere this test does not name, or a surface"
                        + " that names one picks it more than once. A surface answers a reader and"
                        + " says which reader, in one place; everything else is handed the language"
                        + " rather than choosing it.");
    }

    private static int occurrences(String text, String needle) {
        int count = 0;
        for (int at = text.indexOf(needle); at >= 0; at = text.indexOf(needle, at + needle.length())) {
            count++;
        }
        return count;
    }
}
