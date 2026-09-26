package souther.compiler.regex;

/**
 * How a pattern writes a character by its number.
 *
 * <p>Apart from {@link PatternParser} because what it answers is arithmetic on the text rather than
 * grammar: where the digits are, what number they spell, and where a pair of {@code \\u} escapes is
 * one character.
 */
final class PatternEscapes {

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
     * <p>{@code \\uD800\\uDC00} is U+10000 and neither half on its own. A high escape with no low one
     * after it spells the high surrogate, which no {@code String} holds and the reader refuses.
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
}
