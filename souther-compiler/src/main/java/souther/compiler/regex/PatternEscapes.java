package souther.compiler.regex;

/**
 * How a Java pattern writes a character by its number, read the way the engine reads it.
 *
 * <p>Two readers need it. {@link PatternParser} reads the subset of the pattern language this
 * compiler understands, and refuses a quotation or a named character as outside it; the checker
 * asks of every pattern, understood or not, whether it writes a character that is no scalar value
 * ({@link #firstWrittenSurrogate}). Which text an escape spells has one answer, and it is here, so
 * the two cannot read {@code \\uD83D\\uDE00} as one character in one place and two in the other.
 */
public final class PatternEscapes {

    private PatternEscapes() {}

    /**
     * A character an escape spells, and where the escape ends.
     *
     * @param symbol the code point
     * @param end    the index just past the escape
     */
    record Spelled(int symbol, int end) {}

    /**
     * What {@code \\u} spells, read from {@code at}, just past the {@code u}: four hex digits, and
     * where they are a high surrogate followed by a {@code \\u} escape of a low one, the one
     * character the two encode. Null where there are not four hex digits.
     *
     * <p>That is what the engine does: {@code \\uD800\\uDC00} accepts U+10000 and neither half on its
     * own. A high escape with no low one after it spells the high surrogate, which no {@code String}
     * holds.
     */
    static Spelled unicode(String regex, int at) {
        int first = fixedHex(regex, at, 4);
        if (first < 0) {
            return null;
        }
        int next = at + 4;
        if (Character.isHighSurrogate((char) first) && regex.startsWith("\\u", next)) {
            int second = fixedHex(regex, next + 2, 4);
            if (second >= 0 && Character.isLowSurrogate((char) second)) {
                return new Spelled(Character.toCodePoint((char) first, (char) second), next + 6);
            }
        }
        return new Spelled(first, next);
    }

    /**
     * What {@code \x} spells, read from {@code at}, just past the {@code x}: two hex digits, or any
     * number of them in braces up to {@link CodePoints#LAST}. Null where it is neither.
     */
    static Spelled hex(String regex, int at) {
        if (!regex.startsWith("{", at)) {
            int value = fixedHex(regex, at, 2);
            return value < 0 ? null : new Spelled(value, at + 2);
        }
        int value = 0;
        int digits = 0;
        int here = at + 1;
        while (here < regex.length() && regex.charAt(here) != '}') {
            int digit = Character.digit(regex.charAt(here), 16);
            if (digit < 0) {
                return null;
            }
            value = value * 16 + digit;
            digits++;
            if (value > CodePoints.LAST) {
                return null;
            }
            here++;
        }
        if (here >= regex.length() || digits == 0) {
            return null;
        }
        return new Spelled(value, here + 1);
    }

    /** The {@code digits} hex digits at {@code at} as a number, or -1 where they are not there. */
    private static int fixedHex(String regex, int at, int digits) {
        if (at + digits > regex.length()) {
            return -1;
        }
        int value = 0;
        for (int i = at; i < at + digits; i++) {
            int digit = Character.digit(regex.charAt(i), 16);
            if (digit < 0) {
                return -1;
            }
            value = value * 16 + digit;
        }
        return value;
    }

    /**
     * The first escape in {@code regex} that writes half of a surrogate pair, as it is written, or
     * null where none does.
     *
     * <p>Asked of a pattern the engine compiles, and of all of it, including what
     * {@link PatternParser} does not read. The text of a pattern is a {@code String} and holds no
     * surrogate of its own, so what can write one is an escape: {@code \\u} without its other half,
     * {@code \x{...}}, or {@code \N{...}} naming one. What is not an escape is passed over as the
     * engine passes over it — a backslash written before another, and everything between
     * {@code \Q} and {@code \E}, is text rather than an escape.
     *
     * <p>A comment under the {@code x} flag is read as the rest of the pattern is. An escape
     * written there spells nothing to the engine, and is refused all the same: the flag can be
     * turned on and off inside the pattern, and following it is a second reading of the grammar for
     * a case nobody writes.
     */
    public static String firstWrittenSurrogate(String regex) {
        int at = 0;
        while (at < regex.length()) {
            if (regex.charAt(at) != '\\' || at + 1 >= regex.length()) {
                at++;
                continue;
            }
            char kind = regex.charAt(at + 1);
            Spelled spelled = switch (kind) {
                case 'u' -> unicode(regex, at + 2);
                case 'x' -> hex(regex, at + 2);
                case 'N' -> named(regex, at + 2);
                default -> null;
            };
            if (kind == 'Q') {
                int closed = regex.indexOf("\\E", at + 2);
                at = closed < 0 ? regex.length() : closed + 2;
                continue;
            }
            if (spelled == null) {
                // An escape of one character: the backslash and what it was written before.
                at += 2;
                continue;
            }
            if (CodePoints.isSurrogate(spelled.symbol())) {
                return regex.substring(at, spelled.end());
            }
            at = spelled.end();
        }
        return null;
    }

    /** What {@code \N{name}} spells, read from just past the {@code N}, or null where the name is
     *  none Java knows. */
    private static Spelled named(String regex, int at) {
        if (!regex.startsWith("{", at)) {
            return null;
        }
        int closed = regex.indexOf('}', at);
        if (closed < 0) {
            return null;
        }
        try {
            return new Spelled(Character.codePointOf(regex.substring(at + 1, closed)), closed + 1);
        } catch (IllegalArgumentException _) {
            return null;
        }
    }
}
