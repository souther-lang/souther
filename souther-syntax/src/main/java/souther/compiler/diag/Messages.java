package souther.compiler.diag;

import java.text.MessageFormat;
import java.util.Locale;
import java.util.MissingResourceException;
import java.util.ResourceBundle;

/**
 * The diagnostic message catalog. Prose lives in {@code messages.properties} (the English base) and
 * {@code messages_ja.properties}.
 *
 * <p>A key missing from a locale's bundle falls back to the English base, and a key missing from
 * both renders as the key itself, so a half-migrated bundle on a branch still compiles and an
 * unmigrated site never crashes anything. That is a fail-safe and not a way to ship: a catalog that
 * ships defines every key the base defines, which the build holds it to, because a catalog that
 * relies on the fallback answers one diagnostic half in each language.
 *
 * <p>Locale is resolved once, highest precedence first: an explicit {@code --lang} value, the
 * {@code SOUTHER_LANG} environment variable, then English. A language named this way is answered in
 * whether or not the documents are written in it — the reader said which one they read, and the
 * code a diagnostic carries is the same string in every language, so the English documents stay
 * reachable from an answer in any of them.
 *
 * <p>The machine's locale is not consulted. It says which language the machine's own interface is
 * in, which is not evidence about the reader: everything the toolchain ships to read — the
 * specification, the bundled library topics, the CLI's own topics — is written in English, so a
 * reader who chose nothing is answered in the language the answer can be followed up in. Reading
 * the machine instead made the language of the answer depend on where it was run.
 */
public final class Messages {

    private static final String BUNDLE = "souther.compiler.diag.messages";

    private Messages() {
    }

    /** Resolves the locale from an explicit language tag (from {@code --lang}); null means "not set". */
    public static Locale resolveLocale(String explicit) {
        return resolveLocale(explicit, System.getenv("SOUTHER_LANG"));
    }

    /**
     * The precedence itself, over values rather than over where they came from: {@code explicit}
     * wins, then {@code fromEnvironment}, then the default. Either may be null or blank for "not
     * set".
     *
     * <p>Separate from {@link #resolveLocale(String)} so the rule can be asked about without the
     * environment the process happens to be running in answering half of it. The environment is
     * read in one place, and what is done with what it said is a function.
     */
    public static Locale resolveLocale(String explicit, String fromEnvironment) {
        String tag = explicit == null || explicit.isBlank() ? fromEnvironment : explicit;
        if (tag != null && !tag.isBlank()) {
            return Locale.forLanguageTag(tag.replace('_', '-'));
        }
        return defaultLocale();
    }

    /** The locale when none is chosen: English, the one the shipped documents are written in. */
    public static Locale defaultLocale() {
        return Locale.ENGLISH;
    }

    /**
     * Looks up {@code key} for {@code locale} and fills {@code args}. Missing key → the key itself.
     *
     * <p>Every message is rendered as a {@link MessageFormat} pattern, whether or not the site
     * passed anything to put in it. Skipping the rendering for a message that takes no arguments
     * made the catalog's own text mean two different things depending on who read it: a message
     * that quoted a brace so it would survive formatting was shown to the reader with the quotes
     * in it, and a message that did not quote one was a pattern nobody could format. Which of the
     * two a message was is not visible in the message.
     *
     * <p>A pattern the formatter refuses is answered with the text as written. The catalogs are
     * held to being formattable by the build, so this is the fail-safe for one that got through
     * rather than a second way of writing a message: a compiler reporting an error is the worst
     * place to raise another one.
     */
    public static String get(String key, Locale locale, Object... args) {
        String template = lookup(key, locale);
        if (template == null) {
            return key;
        }
        Object[] resolved = new Object[args == null ? 0 : args.length];
        for (int i = 0; i < resolved.length; i++) {
            resolved[i] = args[i] instanceof Localizable l ? get(l.key(), locale, l.args()) : args[i];
        }
        try {
            return new MessageFormat(template, locale).format(resolved);
        } catch (IllegalArgumentException _) {
            return template;
        }
    }

    /** Whether the catalog defines {@code key} for {@code locale} (or its English base). */
    public static boolean has(String key, Locale locale) {
        return lookup(key, locale) != null;
    }

    // No-fallback control so an explicit `--lang en` resolves to the English base rather than being
    // diverted to the JVM default locale's bundle (which ResourceBundle would otherwise insert into
    // the candidate chain). The base bundle stays the final candidate, so a key missing from a
    // locale still falls back to English.
    private static final ResourceBundle.Control CONTROL =
            ResourceBundle.Control.getNoFallbackControl(ResourceBundle.Control.FORMAT_PROPERTIES);

    private static String lookup(String key, Locale locale) {
        try {
            ResourceBundle bundle = ResourceBundle.getBundle(BUNDLE,
                    locale == null ? defaultLocale() : locale, CONTROL);
            return bundle.getString(key);
        } catch (MissingResourceException _) {
            return null;
        }
    }
}
