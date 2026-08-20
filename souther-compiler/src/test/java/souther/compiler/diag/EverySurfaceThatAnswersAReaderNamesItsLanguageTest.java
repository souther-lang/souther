package souther.compiler.diag;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

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
 * <p>A tripwire and not a proof, like the machine-locale test next door. What it reads is the source
 * text, so a locale arriving through a helper, a field of another class, or a method parameter is
 * invisible to it — what it holds is the spelling that would have to be written first, at the file
 * where it would be written. The rest is held by the shape of the API: a message lookup refuses a
 * null locale, so there is no way to be answered in a language without naming one.
 */
class EverySurfaceThatAnswersAReaderNamesItsLanguageTest {

    /**
     * The ways a source picks a language for a diagnostic: the resolution, and every way a
     * {@link Locale} is produced — any of the constants, either factory, and the constructors.
     *
     * <p>Named as a shape rather than as a list of the ones in use, because a list is only as
     * complete as whoever wrote it: {@code Locale.US} is as direct a choice as {@code Locale.ENGLISH}
     * and would have to be thought of to be listed.
     *
     * <p>{@code Locale.ROOT} is not one of them. It is case folding, which is about the bytes and
     * not about a reader.
     */
    private static final Pattern PICKING = Pattern.compile(
            "Messages\\.resolveLocale\\(|Messages\\.defaultLocale\\(\\)"
                    + "|new Locale(?:\\.Builder)?\\b"
                    + "|Locale\\.of\\(|Locale\\.forLanguageTag\\("
                    + "|Locale\\.(?!ROOT\\b)[A-Z][A-Z_]+");

    /** The resolution itself lives here, so this file names languages as its subject matter. */
    private static final String RESOLVER = "souther/compiler/diag/Messages.java";

    /**
     * Every pick in the tree.
     *
     * <p>Four surfaces answer a reader. The CLI, the annotation processor and the build driver
     * resolve — from the flag, from the processor option, and from what a build plugin was asked
     * for; a language server is not told the editor's UI locale, so there is nothing for it to
     * resolve from and it names English outright.
     *
     * <p>The fifth is not a surface. It is the one-line text a {@code CompileException} carries for
     * {@code getMessage()}, which no adapter prints while the exception carries a diagnostic — and
     * the two sites that build it always supply one. It has no reader whose language could be
     * asked, so the language is written where the text is made and no caller can pass one.
     */
    private static final Set<String> NAMED = Set.of(
            "souther/build/driver/CompilerBuildDriver.java picks Messages.resolveLocale(",
            "souther/cli/Main.java picks Messages.resolveLocale(",
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
            Map<String, Integer> counts = new TreeMap<>();
            Matcher found = PICKING.matcher(text);
            while (found.find()) {
                counts.merge(found.group(), 1, Integer::sum);
            }
            counts.forEach((spelling, count) -> picks.add(path + " picks " + spelling
                    + (count == 1 ? "" : " (" + count + " times)")));
        }

        assertEquals(new TreeSet<>(NAMED), picks,
                "a diagnostic's language is picked somewhere this test does not name, or a surface"
                        + " that names one picks it more than once. A surface answers a reader and"
                        + " says which reader, in one place; everything else is handed the language"
                        + " rather than choosing it.");
    }
}
