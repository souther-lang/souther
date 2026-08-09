package souther.compiler.diag.msg;

import java.util.Locale;

/**
 * The catalog entry a {@link Message} renders through, derived from where the message is declared.
 *
 * <p>{@code ImportMessage.NameIsNotAStandardLibraryFunction} is
 * {@code import.name-is-not-a-standard-library-function}: the area comes from the interface the
 * message is declared in, with {@code Message} dropped, and the entry from the message's own name.
 *
 * <p>Derived rather than written beside the message, so that two messages cannot name one entry and
 * a message cannot name none. What that costs is that renaming a message renames its entry, which
 * the build reports as an entry no message names.
 */
public final class MessageKeys {

    private MessageKeys() {
    }

    /** The entry {@code message} renders through. */
    public static String of(Class<?> message) {
        Class<?> area = message.getEnclosingClass();
        if (area == null) {
            throw new IllegalArgumentException("a message is declared in the area it belongs to,"
                    + " and " + message.getName() + " is declared on its own");
        }
        return kebab(dropSuffix(area.getSimpleName())) + "." + kebab(message.getSimpleName());
    }

    private static String dropSuffix(String area) {
        return area.endsWith("Message") ? area.substring(0, area.length() - "Message".length())
                : area;
    }

    /** {@code SpreadFieldCollision} as {@code spread-field-collision}. */
    private static String kebab(String written) {
        StringBuilder out = new StringBuilder(written.length() + 8);
        for (int i = 0; i < written.length(); i++) {
            char c = written.charAt(i);
            if (Character.isUpperCase(c) && i > 0) {
                out.append('-');
            }
            out.append(Character.toLowerCase(c));
        }
        return out.toString().toLowerCase(Locale.ROOT);
    }
}
