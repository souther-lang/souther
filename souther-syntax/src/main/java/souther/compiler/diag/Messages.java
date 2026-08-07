package souther.compiler.diag;

import java.text.MessageFormat;
import java.util.Locale;
import java.util.MissingResourceException;
import java.util.ResourceBundle;

/**
 * The diagnostic message catalog. Prose lives in {@code messages.properties} (the English base) and
 * {@code messages_ja.properties}; a key missing from the Japanese bundle falls back to the English
 * base automatically. A key missing from both renders as the key itself, so a not-yet-migrated site
 * never crashes the compiler.
 *
 * <p>Locale is resolved once, highest precedence first: an explicit {@code --lang} value, the
 * {@code SOUTHER_LANG} environment variable, then English.
 *
 * <p>The JVM default locale is not consulted. It says which language the machine's own interface is
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
        String tag = explicit;
        if (tag == null || tag.isBlank()) {
            tag = System.getenv("SOUTHER_LANG");
        }
        if (tag != null && !tag.isBlank()) {
            return Locale.forLanguageTag(tag.replace('_', '-'));
        }
        return defaultLocale();
    }

    /** The locale when none is chosen: English, the one the shipped documents are written in. */
    public static Locale defaultLocale() {
        return Locale.ENGLISH;
    }

    /** Looks up {@code key} for {@code locale} and fills {@code args}. Missing key → the key itself. */
    public static String get(String key, Locale locale, Object... args) {
        String template = lookup(key, locale);
        if (template == null) {
            return key;
        }
        if (args == null || args.length == 0) {
            return template;
        }
        Object[] resolved = new Object[args.length];
        for (int i = 0; i < args.length; i++) {
            resolved[i] = args[i] instanceof Localizable l ? get(l.key(), locale, l.args()) : args[i];
        }
        return new MessageFormat(template, locale).format(resolved);
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
