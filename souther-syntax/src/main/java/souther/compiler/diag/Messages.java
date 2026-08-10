package souther.compiler.diag;

import souther.compiler.diag.msg.MessageKeys;
import souther.compiler.diag.msg.Message;
import souther.compiler.diag.msg.MessageTemplate;
import souther.compiler.diag.msg.MessageValues;

import java.text.MessageFormat;
import java.util.IllformedLocaleException;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
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
 * <p>What a language may be named by is a language tag, and that is the whole of the rule: a tag no
 * catalog answers is a language nobody has translated this into yet and falls back to the base, and
 * a tag that is not one is not a language at all. The two are separate questions and a caller asks
 * the second with {@link #namesALanguage} — an answer in English is what naming a language with no
 * catalog gets, and it must not also be what naming nothing gets.
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

    /** Where a language is named when the command line names none. */
    public static final String ENVIRONMENT_VARIABLE = "SOUTHER_LANG";

    /**
     * The tag this invocation names its language with, and whether it was the environment that named
     * it rather than the line.
     *
     * <p>The two are answered together because a caller refusing the tag has to say where it was
     * written: a reader told that {@code --lang} is malformed when what is malformed is a variable
     * their shell exports is sent to fix something they did not write.
     */
    public record Named(String tag, boolean fromEnvironment) {}

    /** Resolves the locale from an explicit language tag (from {@code --lang}); null means "not set". */
    public static Locale resolveLocale(String explicit) {
        return resolveLocale(explicit, System.getenv(ENVIRONMENT_VARIABLE));
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
        return resolveLocale(namedLanguage(explicit, fromEnvironment));
    }

    /**
     * The locale of whatever named the language, or the default where nothing did.
     *
     * <p>Where the precedence has already been settled — a caller that reads an option knows whether
     * it was written, which is more than the value of it says, and answers that question once rather
     * than once here and once where it refuses. Nothing is reached for beyond what is named: a tag
     * this cannot read resolves to what {@link Locale#forLanguageTag} leaves of it, which is the
     * default for a tag with nothing readable in front, and never to the value that was outranked.
     */
    public static Locale resolveLocale(Named named) {
        return named == null ? defaultLocale() : Locale.forLanguageTag(asLanguageTag(named.tag()));
    }

    /** As {@link #namedLanguage(String, String)}, with the environment this process is running in. */
    public static Named namedLanguage(String explicit) {
        return namedLanguage(explicit, System.getenv(ENVIRONMENT_VARIABLE));
    }

    /**
     * Which tag the precedence chose and where it was written, or null where nothing named a
     * language.
     *
     * <p>The one a caller holds to being a language tag, and the only one: the value that lost the
     * precedence is not read, and a caller refusing it would be stating that every language anything
     * on this machine names has to be well formed, which is a different rule from the one that says
     * which of them is used. {@code SOUTHER_LANG=!! souther compile x.sou --lang en} is a line that
     * names English, and it compiles.
     *
     * <p>Blank is not a language named, on either side, which is the rule {@link #resolveLocale}
     * resolves by and is stated once for both. A shell exports a variable empty to unset it, and an
     * adapter passing an option through has nothing to pass when nobody wrote one.
     *
     * <p>That a command line's {@code --lang} was written at all is not something this can be asked:
     * a blank value arrives here as the blank that means nothing was named. Whoever read the option
     * knows whether it was there, and holds it to being a tag before asking this — {@code --lang ''}
     * is somebody writing a value where a language goes, and answering it from the environment is
     * answering a line in a language it did not ask for.
     */
    public static Named namedLanguage(String explicit, String fromEnvironment) {
        if (explicit != null && !explicit.isBlank()) {
            return new Named(explicit, false);
        }
        if (fromEnvironment != null && !fromEnvironment.isBlank()) {
            return new Named(fromEnvironment, true);
        }
        return null;
    }

    /**
     * Whether the whole of {@code tag} is a language tag, which is what a caller asks before naming
     * a language with it.
     *
     * <p>Asked of {@link Locale.Builder}, which refuses a tag it cannot read, and not of
     * {@link Locale#forLanguageTag}, which is written to be tolerant: given a subtag it cannot read
     * it keeps the well-formed part in front of it and drops the rest, so {@code en-!!} arrives as
     * English and the reader is never told that what they wrote after {@code en} said nothing. That
     * tolerance is what makes it the right thing to resolve with — a caller past this point has a
     * tag — and the wrong thing to check with.
     *
     * <p>Well formed, and not one of the languages this toolchain ships a catalog for. Which
     * languages are answered in is decided by which catalogs are on the class path and falls back to
     * the base one; that a reader named a language nobody has translated yet is not a mistake in
     * what they wrote. So {@code fr}, {@code und} and a private-use {@code x-souther} are all tags,
     * and all are answered in English until a catalog for them ships.
     */
    public static boolean namesALanguage(String tag) {
        if (tag.isBlank()) {
            // Said here rather than left to the builder, which does not answer it the same way
            // everywhere: on 25 an empty tag is a subtag that is missing and is refused, and on 26 it
            // resets the builder and comes back as `und`. A rule about what a reader may write is not
            // one the runtime underneath gets to decide.
            return false;
        }
        try {
            new Locale.Builder().setLanguageTag(asLanguageTag(tag));
            return true;
        } catch (IllformedLocaleException _) {
            return false;
        }
    }

    /**
     * The tag as BCP 47 spells it: an underscore is read as the hyphen it stands in for, so that
     * {@code ja_JP} — how a POSIX locale writes the same thing, and what a reader copying one out of
     * their environment has to hand — names Japanese in Japan.
     *
     * <p>The alias and nothing else. What it produces is held to being a language tag like any
     * other, so {@code ja_JP.UTF-8} is refused: the codeset a POSIX locale carries is not part of
     * naming a language, and reading the tag up to it and dropping the rest is the silence this is
     * spelt out to avoid.
     */
    private static String asLanguageTag(String tag) {
        return tag.replace('_', '-');
    }

    /**
     * The locale when none is chosen: English, the one the shipped documents are written in.
     *
     * <p>Not callable from outside. It is the tail of the resolution above and nothing else: it
     * answers the reader who named no language. Offered as a way to get a locale it reads as one,
     * and a caller that needs a value but has no reader to resolve for takes it — after which that
     * caller's text changes language the next time the default is decided, which is a decision
     * about readers who named nothing and not about that caller.
     */
    private static Locale defaultLocale() {
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
        Objects.requireNonNull(locale, NEEDS_A_LANGUAGE);
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

    /**
     * Renders {@code message} by putting each value it carries where its catalog entry names it.
     *
     * <p>The names are the message's own components — {@code {field}}, not {@code {0}} — so a
     * reader of the entry can tell what goes where, and the build can hold the entry to naming every
     * one of them. Two entries take five values and thirteen take four; at that width a number is a
     * spelling only the site it was written beside can decode.
     *
     * <p>A missing entry renders as its key, as a keyed lookup does: a compiler reporting an error
     * is the worst place to raise another one.
     */
    public static String render(Message message, Locale locale) {
        Objects.requireNonNull(locale, NEEDS_A_LANGUAGE);
        String template = lookup(MessageKeys.of(message), locale);
        if (template == null) {
            return MessageKeys.of(message);
        }
        Map<String, Object> values = MessageValues.of(message);
        StringBuilder out = new StringBuilder(template.length() + 32);
        for (MessageTemplate.Part part : MessageTemplate.parse(template).parts()) {
            switch (part) {
                case MessageTemplate.Part.Text text -> out.append(text.written());
                case MessageTemplate.Part.Value value ->
                        out.append(text(values.get(value.name()), locale));
                // The build refuses these, so what is left here is a catalog that got past it. Show
                // it as written rather than raising: a compiler reporting an error is the worst
                // place to raise another one.
                case MessageTemplate.Part.Malformed bad -> out.append(bad.written());
            }
        }
        return out.toString();
    }

    /**
     * One value of a message as text.
     *
     * <p>A value written in the catalog itself — the kind of element an operation needs, which is a
     * phrase and not a name — is rendered in the language the message is being asked in, as it was
     * when the values were an array. Everything else is what it prints as.
     */
    public static String text(Object value, Locale locale) {
        return value instanceof Localizable l ? get(l.key(), locale, l.args()) : String.valueOf(value);
    }

    /** Whether the catalog defines {@code key} for {@code locale} (or its English base). */
    public static boolean has(String key, Locale locale) {
        Objects.requireNonNull(locale, NEEDS_A_LANGUAGE);
        return lookup(key, locale) != null;
    }

    /**
     * What a caller passing no locale is told.
     *
     * <p>No locale is not the default one. Reading it that way puts the default back within reach of
     * every caller — a site with no reader to resolve for passes nothing and is answered out of the
     * language chosen for readers who named none, which is the same mistake a public
     * {@link #defaultLocale()} allowed, spelled so that nothing looking for a locale being picked
     * would see it. A caller either resolved a language for a reader or is building text that has no
     * reader, and the second has {@link DiagnosticRenderer#legacyBody}.
     */
    static final String NEEDS_A_LANGUAGE =
            "a message is written in a language, and no language is not one of them:"
                    + " resolve one for the reader, or take the body that has no reader";

    // No-fallback control so an explicit `--lang en` resolves to the English base rather than being
    // diverted to the JVM default locale's bundle (which ResourceBundle would otherwise insert into
    // the candidate chain). The base bundle stays the final candidate, so a key missing from a
    // locale still falls back to English.
    private static final ResourceBundle.Control CONTROL =
            ResourceBundle.Control.getNoFallbackControl(ResourceBundle.Control.FORMAT_PROPERTIES);

    private static String lookup(String key, Locale locale) {
        try {
            ResourceBundle bundle = ResourceBundle.getBundle(BUNDLE, locale, CONTROL);
            return bundle.getString(key);
        } catch (MissingResourceException _) {
            return null;
        }
    }
}
