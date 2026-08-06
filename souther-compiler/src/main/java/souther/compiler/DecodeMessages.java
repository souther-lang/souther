package souther.compiler;

import net.unit8.raoh.Issue;
import net.unit8.raoh.Issues;
import net.unit8.raoh.MessageResolver;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.MissingResourceException;
import java.util.ResourceBundle;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * The decoder's issues in the reader's language. Every issue arrives already written — the decoder
 * states the rule the value broke, in English — and marked as the catalog's to replace, so the same
 * thing can be said in the language the command line selected.
 *
 * <p>Replacing it is only worth doing where the catalog entry says as much. An entry is one template
 * per code, and a code covers more shapes than a template can state: {@code out_of_range} is
 * reported for a lower bound alone, an upper bound alone, and a range, while the template names both
 * ends. Substituting it against metadata that carries one end leaves the other as the literal
 * {@code {max}}, which tells the reader there is a bound where there is none. A code the catalog does
 * not carry at all — {@code invariant_violation}, which every rule no constraint states reports —
 * has nothing to substitute, and resolving it yields the code's own name.
 *
 * <p>So an entry applies when its placeholders are all ones the issue's metadata fills, and the
 * decoder's own message stands when it does not. The check is on the template rather than on the
 * result: a value may itself contain braces, and by then what put them there is no longer visible.
 */
final class DecodeMessages {

    private DecodeMessages() {}

    /** The decoder's own message catalog, which its issues are written against. */
    private static final String CATALOG = "net.unit8.raoh.messages";

    /**
     * The lookup the decoder's own resolver does: the requested locale, then the base bundle. Without
     * this, asking for English on a machine whose default locale is Japanese answers from the
     * Japanese bundle.
     */
    private static final ResourceBundle.Control NO_FALLBACK =
            ResourceBundle.Control.getNoFallbackControl(ResourceBundle.Control.FORMAT_PROPERTIES);

    /** A template's named placeholder, which is a metadata key. */
    private static final Pattern PLACEHOLDER = Pattern.compile("\\{([A-Za-z][A-Za-z0-9_]*)}");

    /** Every issue with the message its reader gets, in {@code locale}. */
    static Issues localize(Issues issues, Locale locale) {
        List<Issue> out = new ArrayList<>();
        for (Issue issue : issues.asList()) {
            String message = message(issue, locale);
            out.add(message.equals(issue.message()) ? issue : issue.withCustomMessage(message));
        }
        return new Issues(List.copyOf(out));
    }

    private static String message(Issue issue, Locale locale) {
        if (issue.customMessage()) {
            return issue.message();
        }
        String template = template(issue.code(), locale);
        if (template == null || !issue.meta().keySet().containsAll(placeholders(template))) {
            return issue.message();
        }
        return MessageResolver.interpolate(template, issue.meta());
    }

    /** The catalog's entry for {@code code} in {@code locale}, or null where it carries none. */
    private static String template(String code, Locale locale) {
        try {
            return ResourceBundle.getBundle(CATALOG, locale, NO_FALLBACK)
                    .getString(MessageResolver.KEY_PREFIX + code);
        } catch (MissingResourceException _) {
            return null;
        }
    }

    /** The metadata keys the template needs before it states anything true. */
    private static Set<String> placeholders(String template) {
        Set<String> names = new LinkedHashSet<>();
        Matcher m = PLACEHOLDER.matcher(template);
        while (m.find()) {
            names.add(m.group(1));
        }
        return names;
    }
}
