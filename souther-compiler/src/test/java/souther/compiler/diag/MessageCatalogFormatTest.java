package souther.compiler.diag;

import org.junit.jupiter.api.Test;

import souther.compiler.Prelude;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Properties;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Every message in the catalog is a {@link java.text.MessageFormat} pattern, where a lone {@code '}
 * opens a quoted run and {@code ''} is the apostrophe itself. A message that writes {@code a data's}
 * therefore quotes the whole rest of itself: the apostrophe disappears and every {@code {n}} after it
 * renders literally, as the placeholder rather than the value.
 *
 * <p>Nothing caught that, because a message is only read when its diagnostic fires and the result is
 * prose nobody diffs. This renders each one with stand-in arguments and fails on any placeholder that
 * survived.
 */
class MessageCatalogFormatTest {

    private static final Pattern PLACEHOLDER = Pattern.compile("\\{(\\d)}");

    @Test
    void everyEnglishMessageSubstitutesAllOfItsArguments() throws IOException {
        assertEquals(List.of(), unsubstituted("/souther/compiler/diag/messages.properties", Locale.ENGLISH));
    }

    @Test
    void everyJapaneseMessageSubstitutesAllOfItsArguments() throws IOException {
        assertEquals(List.of(),
                unsubstituted("/souther/compiler/diag/messages_ja.properties", Locale.JAPANESE));
    }

    /** The keys whose rendering still contains a {@code {n}} — one per line, so a failure names them
     *  all rather than the first. */
    private static List<String> unsubstituted(String resource, Locale locale) throws IOException {
        Properties catalog = new Properties();
        try (InputStream in = MessageCatalogFormatTest.class.getResourceAsStream(resource)) {
            catalog.load(new InputStreamReader(in, StandardCharsets.UTF_8));
        }
        List<String> broken = new ArrayList<>();
        for (String key : catalog.stringPropertyNames()) {
            String template = catalog.getProperty(key);
            int arity = arityOf(template);
            if (arity == 0) {
                continue;
            }
            Object[] args = new Object[arity];
            for (int i = 0; i < arity; i++) {
                args[i] = "<arg" + i + ">";
            }
            String rendered = Messages.get(key, locale, args);
            if (PLACEHOLDER.matcher(rendered).find()) {
                broken.add(key + " -> " + rendered);
            }
        }
        broken.sort(String::compareTo);
        return broken;
    }

    /** One past the highest argument index the pattern names. */
    private static int arityOf(String template) {
        Matcher m = PLACEHOLDER.matcher(template);
        int highest = -1;
        while (m.find()) {
            highest = Math.max(highest, Integer.parseInt(m.group(1)));
        }
        return highest + 1;
    }

    /**
     * A key the compiler names but the catalog does not define renders as the key itself, so the
     * reader gets {@code check.match.newtype.notnewtype} where the message belongs. Nothing else
     * catches it: the site compiles, and the text is only read when that diagnostic fires.
     *
     * <p>The keys are collected from the sources rather than from the call sites, because a key is
     * also passed to the parser's and the AST builder's own {@code error(...)} helpers, and those
     * sites are invisible to a scan for {@code Diagnostic.of}. A string literal counts as a key when
     * it is shaped like one and its first segment is one the catalog already uses — so the very
     * first key of a brand-new namespace is the one case this does not see.
     */
    @Test
    void everyKeyTheCompilerNamesIsInTheCatalog() throws IOException {
        Set<String> defined = keysOf("/souther/compiler/diag/messages.properties");
        Set<String> namespaces = new TreeSet<>();
        for (String key : defined) {
            namespaces.add(key.substring(0, key.indexOf('.')));
        }
        Set<String> named = new TreeSet<>();
        for (Path source : mainSources()) {
            Matcher m = KEY_LITERAL.matcher(Files.readString(source, StandardCharsets.UTF_8));
            while (m.find()) {
                String key = m.group(1);
                if (namespaces.contains(key.substring(0, key.indexOf('.')))) {
                    named.add(key);
                }
            }
        }
        assertFalse(named.isEmpty(), "found no message keys at all — the source scan missed the tree");
        named.removeAll(defined);
        assertEquals(Set.of(), named);
    }

    /**
     * The other direction, over the one namespace where it holds: an example message the catalog
     * defines and nothing shows.
     *
     * <p>Narrower than the check above on purpose. Elsewhere a key is often built from parts — a
     * title from a code, a kind from a type — and a scan for literals cannot see those. Here every
     * key is written out at the site that uses it, which is what makes a hint nobody attaches
     * findable at all. That is the mistake this catches: a hint added beside a new message and never
     * passed to the diagnostic renders nowhere, and the message still reads fine on its own.
     */
    @Test
    void noExampleMessageIsDefinedAndNeverShown() throws IOException {
        Set<String> named = new TreeSet<>();
        for (Path source : mainSources()) {
            Matcher m = KEY_LITERAL.matcher(Files.readString(source, StandardCharsets.UTF_8));
            while (m.find()) {
                named.add(m.group(1));
            }
        }
        Set<String> unshown = new TreeSet<>();
        for (String key : keysOf("/souther/compiler/diag/messages.properties")) {
            if (key.startsWith("check.example.") && !named.contains(key)) {
                unshown.add(key);
            }
        }
        assertEquals(Set.of(), unshown);
    }

    @Test
    void bothCatalogsDefineTheSameKeys() throws IOException {
        Set<String> english = keysOf("/souther/compiler/diag/messages.properties");
        Set<String> japanese = keysOf("/souther/compiler/diag/messages_ja.properties");
        Set<String> onlyEnglish = new TreeSet<>(english);
        onlyEnglish.removeAll(japanese);
        Set<String> onlyJapanese = new TreeSet<>(japanese);
        onlyJapanese.removeAll(english);
        assertEquals(Set.of(), onlyEnglish, "defined in English only");
        assertEquals(Set.of(), onlyJapanese, "defined in Japanese only");
    }

    private static final Pattern KEY_LITERAL =
            Pattern.compile("\"([a-z][a-z0-9]*(?:\\.[a-z0-9]+)+)\"");

    private static Set<String> keysOf(String resource) throws IOException {
        Properties catalog = new Properties();
        try (InputStream in = MessageCatalogFormatTest.class.getResourceAsStream(resource)) {
            catalog.load(new InputStreamReader(in, StandardCharsets.UTF_8));
        }
        return new TreeSet<>(catalog.stringPropertyNames());
    }

    /** Every module's main sources. The test runs in its own module directory, so the repo root is
     *  that directory's parent, and any module may name a message key. */
    static List<Path> mainSources() throws IOException {
        Path module = Path.of("").toAbsolutePath();
        Path repo = Files.isDirectory(module.resolve(Path.of("src", "main", "java")))
                ? module.getParent() : module;
        List<Path> sources = new ArrayList<>();
        try (Stream<Path> modules = Files.list(repo)) {
            for (Path root : modules.map(m -> m.resolve(Path.of("src", "main", "java"))).toList()) {
                if (!Files.isDirectory(root)) {
                    continue;
                }
                try (Stream<Path> walk = Files.walk(root)) {
                    walk.filter(p -> p.toString().endsWith(".java")).forEach(sources::add);
                }
            }
        }
        return sources;
    }

    @Test
    void noEnglishKeyIsDefinedTwice() throws IOException {
        assertEquals(List.of(), duplicateKeys("/souther/compiler/diag/messages.properties"));
    }

    @Test
    void noJapaneseKeyIsDefinedTwice() throws IOException {
        assertEquals(List.of(), duplicateKeys("/souther/compiler/diag/messages_ja.properties"));
    }

    @Test
    void everyStandardLibraryFunctionADiagnosticNamesExists() throws IOException {
        assertEquals(Set.of(), missingLibraryNames("/souther/compiler/diag/messages.properties"));
    }

    @Test
    void theJapaneseCatalogNamesTheSameOnes() throws IOException {
        assertEquals(Set.of(), missingLibraryNames("/souther/compiler/diag/messages_ja.properties"));
    }

    /**
     * The qualified standard-library names this catalog quotes that the library does not publish.
     *
     * <p>A hint that tells an author to reach for {@code List.flatMap} after it was renamed sends
     * them to a compile error, in the one text whose whole job is to get them out of one. Nothing
     * else notices: the catalog is prose, so a rename sweeps the code and the tests and leaves the
     * advice behind — which is exactly what happened to two hints here, found in review rather than
     * by a build.
     *
     * <p>Only a name under a library qualifier is checked, and only where the catalog wrote it as
     * code. A qualifier the library does not have is somebody's module and not this test's business.
     */
    private static Set<String> missingLibraryNames(String resource) throws IOException {
        Pattern quoted = Pattern.compile("`([A-Z][A-Za-z]*)\\.([a-zA-Z_][A-Za-z0-9_]*)`");
        Set<String> missing = new TreeSet<>();
        try (InputStream in = MessageCatalogFormatTest.class.getResourceAsStream(resource);
                BufferedReader lines =
                        new BufferedReader(new InputStreamReader(in, StandardCharsets.UTF_8))) {
            String line;
            while ((line = lines.readLine()) != null) {
                Matcher m = quoted.matcher(line);
                while (m.find()) {
                    if (!Prelude.isQualifier(m.group(1))) {
                        continue;
                    }
                    String qualified = m.group(1) + "." + m.group(2);
                    if (!Prelude.published().contains(qualified)) {
                        missing.add(qualified);
                    }
                }
            }
        }
        return Set.copyOf(missing);
    }

    /**
     * The keys this catalog defines more than once. A second definition silently wins, so the first
     * one is dead and whichever diagnostics meant it render someone else's text — the same kind of
     * defect as the one above, and just as invisible for the same reason.
     *
     * <p>Read line by line rather than through {@link Properties}, which keeps only the last value
     * and so cannot see the collision at all. The catalog uses no line continuations, so a line
     * carrying an {@code =} outside a comment is a definition.
     */
    private static List<String> duplicateKeys(String resource) throws IOException {
        Set<String> seen = new LinkedHashSet<>();
        Set<String> duplicated = new TreeSet<>();
        try (InputStream in = MessageCatalogFormatTest.class.getResourceAsStream(resource);
                BufferedReader lines =
                        new BufferedReader(new InputStreamReader(in, StandardCharsets.UTF_8))) {
            String line;
            while ((line = lines.readLine()) != null) {
                String trimmed = line.strip();
                int eq = trimmed.indexOf('=');
                if (trimmed.isEmpty() || trimmed.startsWith("#") || eq < 0) {
                    continue;
                }
                String key = trimmed.substring(0, eq).strip();
                if (!seen.add(key)) {
                    duplicated.add(key);
                }
            }
        }
        return List.copyOf(duplicated);
    }
}
