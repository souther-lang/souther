package souther.compiler.diag;

import org.junit.jupiter.api.Test;

import souther.compiler.Prelude;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Properties;
import java.util.ResourceBundle;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Every catalog that ships is complete on its own and valid on its own.
 *
 * <p>The checks here used to name the English and the Japanese catalog, one literal path each. A
 * third catalog therefore shipped with nothing said about it: a file of three keys quoting a
 * standard-library name that no longer exists passed every one of them, and a compile run in that
 * language answered with its message body translated and its title, its hint and every key it did
 * not define still in English. {@link ResourceBundle} falls back to the base for a key a locale is
 * missing, which is what turns an incomplete catalog into one answer written half in each language
 * rather than into a visible failure.
 *
 * <p>So the quantifier is over the catalog files that ship, discovered from the tree, and not over a
 * list of locales somebody has to remember to extend. A catalog added tomorrow is under all of this
 * the moment it is written.
 *
 * <p>The fallback stays: a key missing from both catalogs still renders as itself rather than
 * stopping a compile, and a bundle half-migrated on a branch still runs. What it no longer is, is
 * how a shipped catalog is allowed to be incomplete.
 */
class EveryShippedMessageCatalogIsCompleteAndValidTest {

    /** Where the bundle {@link Messages} reads lives, as a path under a module's resources. */
    private static final String PACKAGE = "souther/compiler/diag";
    /** The bundle's own name, so the base catalog is {@code messages.properties}. */
    private static final String BUNDLE = "messages";
    private static final String SUFFIX = ".properties";

    /**
     * The same control {@link Messages} looks a bundle up with, used here to spell a locale back
     * into the file name it would be read from.
     */
    private static final ResourceBundle.Control CONTROL =
            ResourceBundle.Control.getNoFallbackControl(ResourceBundle.Control.FORMAT_PROPERTIES);

    private static final Pattern PLACEHOLDER = Pattern.compile("\\{(\\d)}");

    /**
     * A catalog that ships: the file, and the language its messages are written in.
     *
     * <p>The base file carries no language in its name. To {@link ResourceBundle} it is the root
     * bundle, which is a fallback rather than a language; to Souther it is the English catalog,
     * which is what {@link Messages#defaultLocale()} says and what makes "the same keys as the base"
     * a statement about a language rather than about a default.
     */
    private record Catalog(Path path, Locale locale) {

        String name() {
            return path.getFileName().toString();
        }

        boolean isBase() {
            return name().equals(BUNDLE + SUFFIX);
        }
    }

    @Test
    void exactlyOneCatalogIsTheBase() throws IOException {
        List<String> bases = new ArrayList<>();
        for (Catalog catalog : catalogs()) {
            if (catalog.isBase()) {
                bases.add(catalog.path().toString());
            }
        }
        assertEquals(1, bases.size(),
                "the base catalog is what every other one is compared against, and what a key"
                        + " missing everywhere else falls back to: " + bases);
    }

    /**
     * A catalog is named for the locale it will be read as. The name is the only place a shipped
     * file says which language it is in, so a name {@link ResourceBundle} resolves differently than
     * this test reads it would leave the checks below describing a locale nobody is ever answered
     * in — spelling the locale back through the same control is what closes that.
     */
    @Test
    void everyCatalogIsNamedForTheLocaleItIsReadAs() throws IOException {
        Set<String> misnamed = new TreeSet<>();
        for (Catalog catalog : catalogs()) {
            if (catalog.isBase()) {
                continue;
            }
            String reachedAs = CONTROL.toBundleName(BUNDLE, catalog.locale()) + SUFFIX;
            if (!reachedAs.equals(catalog.name())) {
                misnamed.add(catalog.name() + " is read as " + catalog.locale().toLanguageTag()
                        + ", which is looked up as " + reachedAs);
            }
        }
        assertEquals(Set.of(), misnamed, "a catalog's name and the locale it is reached by disagree");
    }

    /**
     * The invariant the fallback used to stand in for. A shipped catalog defines every key the base
     * defines, so a reader who chose that language is answered in it throughout one diagnostic —
     * title, message, labels and hint — rather than in whichever of the two languages each key
     * happened to have reached.
     */
    @Test
    void everyCatalogDefinesTheSameKeysAsTheBase() throws IOException {
        Set<String> base = keysOf(baseCatalog().path());
        Set<String> divergent = new TreeSet<>();
        for (Catalog catalog : catalogs()) {
            if (catalog.isBase()) {
                continue;
            }
            Set<String> keys = keysOf(catalog.path());
            for (String key : difference(base, keys)) {
                divergent.add(catalog.name() + " does not define " + key);
            }
            for (String key : difference(keys, base)) {
                divergent.add(catalog.name() + " defines " + key + ", which the base does not");
            }
        }
        assertEquals(Set.of(), divergent);
    }

    /**
     * Every message is a {@link MessageFormat} pattern, where a lone {@code '} opens a quoted run
     * and {@code ''} is the apostrophe itself. A message that writes {@code a data's} therefore
     * quotes the whole rest of itself: the apostrophe disappears and every {@code {n}} after it
     * renders literally, as the placeholder rather than the value.
     *
     * <p>Nothing caught that, because a message is only read when its diagnostic fires and the
     * result is prose nobody diffs. This renders each one with stand-in arguments and fails on any
     * placeholder that survived.
     *
     * <p>Rendered from the catalog's own text rather than through {@link Messages#get}, which reads
     * the bundle and so can answer with the base's copy of a key. A check that a file is valid has
     * to have read that file.
     */
    @Test
    void everyCatalogSubstitutesAllOfItsArguments() throws IOException {
        List<String> broken = new ArrayList<>();
        for (Catalog catalog : catalogs()) {
            Properties messages = load(catalog.path());
            for (String key : messages.stringPropertyNames()) {
                String template = messages.getProperty(key);
                int arity = arityOf(template);
                if (arity == 0) {
                    continue;
                }
                Object[] args = new Object[arity];
                for (int i = 0; i < arity; i++) {
                    args[i] = "<arg" + i + ">";
                }
                String rendered = new MessageFormat(template, catalog.locale()).format(args);
                if (PLACEHOLDER.matcher(rendered).find()) {
                    broken.add(catalog.name() + ": " + key + " -> " + rendered);
                }
            }
        }
        broken.sort(String::compareTo);
        assertEquals(List.of(), broken);
    }

    @Test
    void noCatalogDefinesAKeyTwice() throws IOException {
        List<String> duplicated = new ArrayList<>();
        for (Catalog catalog : catalogs()) {
            for (String key : duplicateKeys(catalog.path())) {
                duplicated.add(catalog.name() + ": " + key);
            }
        }
        assertEquals(List.of(), duplicated);
    }

    @Test
    void everyCatalogNamesOnlyStandardLibraryFunctionsThatExist() throws IOException {
        Set<String> missing = new TreeSet<>();
        for (Catalog catalog : catalogs()) {
            for (String name : missingLibraryNames(catalog.path())) {
                missing.add(catalog.name() + ": " + name);
            }
        }
        assertEquals(Set.of(), missing);
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
     *
     * <p>Against the base, which every other catalog is held to define exactly.
     */
    @Test
    void everyKeyTheCompilerNamesIsInTheCatalog() throws IOException {
        Set<String> defined = keysOf(baseCatalog().path());
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
        for (String key : keysOf(baseCatalog().path())) {
            if (key.startsWith("check.example.") && !named.contains(key)) {
                unshown.add(key);
            }
        }
        assertEquals(Set.of(), unshown);
    }

    /**
     * The same question over every namespace, not just the example one: a message the catalog
     * defines and nothing names is a message no compile can show. Four of them were found by
     * reading rather than by a build while the codes were being assigned, and two of those had a
     * rule written for them in the specification off the strength of text nobody could reach.
     *
     * <p>Held to the keys a site writes out. A key built by concatenation is invisible to a scan of
     * literals and would read as unused: the hints, which are `+<key> + ".hint"+` at several sites,
     * and the two namespaces whose leaf is chosen at run time.
     */
    @Test
    void noMessageIsDefinedAndNeverShown() throws IOException {
        Set<String> named = new TreeSet<>();
        for (Path source : mainSources()) {
            Matcher m = KEY_LITERAL.matcher(Files.readString(source, StandardCharsets.UTF_8));
            while (m.find()) {
                named.add(m.group(1));
            }
        }
        Set<String> unshown = new TreeSet<>();
        for (String key : keysOf(baseCatalog().path())) {
            if (key.endsWith(".hint") || key.startsWith("check.typearg.") || key.startsWith("kind.")
                    || named.contains(key)) {
                continue;
            }
            unshown.add(key);
        }
        assertEquals(Set.of(), unshown, "defined and unreachable — nothing can show these");
    }

    private static final Pattern KEY_LITERAL =
            Pattern.compile("\"([a-z][a-z0-9]*(?:\\.[a-z0-9]+)+)\"");

    /**
     * The catalogs that ship, found in the tree rather than listed here. Read off the repository
     * because that is what "shipped" is decided by: a file under a module's resources, in the
     * package the bundle is read from, is in the jar and is reachable by whoever names its language.
     */
    private static List<Catalog> catalogs() throws IOException {
        List<Catalog> found = new ArrayList<>();
        for (Path resources : moduleDirectories("resources")) {
            Path directory = resources.resolve(PACKAGE);
            if (!Files.isDirectory(directory)) {
                continue;
            }
            try (Stream<Path> files = Files.list(directory)) {
                for (Path file : files.sorted().toList()) {
                    String name = file.getFileName().toString();
                    if (name.startsWith(BUNDLE) && name.endsWith(SUFFIX)) {
                        found.add(new Catalog(file, localeOf(name)));
                    }
                }
            }
        }
        return List.copyOf(found);
    }

    private static Catalog baseCatalog() throws IOException {
        for (Catalog catalog : catalogs()) {
            if (catalog.isBase()) {
                return catalog;
            }
        }
        throw new IllegalStateException("no base catalog was found; the scan missed the tree");
    }

    /** The language a catalog file's name says it is in. The base names none and is English. */
    private static Locale localeOf(String name) {
        String stem = name.substring(0, name.length() - SUFFIX.length());
        String tag = stem.substring(BUNDLE.length());
        return tag.isEmpty()
                ? Messages.defaultLocale()
                : Locale.forLanguageTag(tag.substring(1).replace('_', '-'));
    }

    /** Every module's main sources. Any module may name a message key. */
    static List<Path> mainSources() throws IOException {
        List<Path> sources = new ArrayList<>();
        for (Path root : moduleDirectories("java")) {
            try (Stream<Path> walk = Files.walk(root)) {
                walk.filter(p -> p.toString().endsWith(".java")).forEach(sources::add);
            }
        }
        return sources;
    }

    /** Every module's {@code src/main/<kind>}, for the modules that have one. The test runs in its
     *  own module directory, so the repository root is that directory's parent. */
    private static List<Path> moduleDirectories(String kind) throws IOException {
        Path module = Path.of("").toAbsolutePath();
        Path repo = Files.isDirectory(module.resolve(Path.of("src", "main", "java")))
                ? module.getParent() : module;
        List<Path> directories = new ArrayList<>();
        try (Stream<Path> modules = Files.list(repo)) {
            for (Path candidate : modules.map(m -> m.resolve(Path.of("src", "main", kind))).toList()) {
                if (Files.isDirectory(candidate)) {
                    directories.add(candidate);
                }
            }
        }
        directories.sort(Path::compareTo);
        return directories;
    }

    private static Properties load(Path catalog) throws IOException {
        Properties messages = new Properties();
        try (BufferedReader text = Files.newBufferedReader(catalog, StandardCharsets.UTF_8)) {
            messages.load(text);
        }
        return messages;
    }

    private static Set<String> keysOf(Path catalog) throws IOException {
        return new TreeSet<>(load(catalog).stringPropertyNames());
    }

    private static Set<String> difference(Set<String> from, Set<String> without) {
        Set<String> left = new TreeSet<>(from);
        left.removeAll(without);
        return left;
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
    private static Set<String> missingLibraryNames(Path catalog) throws IOException {
        Pattern quoted = Pattern.compile("`([A-Z][A-Za-z]*)\\.([a-zA-Z_][A-Za-z0-9_]*)`");
        Set<String> missing = new TreeSet<>();
        for (String line : Files.readAllLines(catalog, StandardCharsets.UTF_8)) {
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
    private static List<String> duplicateKeys(Path catalog) throws IOException {
        Set<String> seen = new LinkedHashSet<>();
        Set<String> duplicated = new TreeSet<>();
        try (BufferedReader lines = Files.newBufferedReader(catalog, StandardCharsets.UTF_8)) {
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
