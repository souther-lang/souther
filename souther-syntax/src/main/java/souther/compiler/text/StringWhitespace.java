package souther.compiler.text;

/**
 * String whitespace (spec §string-whitespace) as the syntax reads it: the fixed set of code points
 * {@code trim} and {@code words} scan by, for a rule of the grammar that asks whether a string
 * literal holds anything but whitespace.
 *
 * <p>The set is enumerated rather than read off a platform table, so a Unicode update in the JVM
 * does not change what the grammar admits. The runtime holds the same set for {@code trim}; the
 * syntax cannot see the runtime, so the compiler's tests hold the two against each other.
 */
public final class StringWhitespace {

    private StringWhitespace() {}

    /** Whether {@code codePoint} is String whitespace. */
    public static boolean isWhitespace(int codePoint) {
        return switch (codePoint) {
            case 0x0009, 0x000A, 0x000B, 0x000C, 0x000D,
                 0x0020,
                 0x0085,
                 0x00A0,
                 0x1680,
                 0x2028, 0x2029,
                 0x202F,
                 0x205F,
                 0x3000 -> true;
            default -> codePoint >= 0x2000 && codePoint <= 0x200A;
        };
    }

    /** Whether {@code text} holds nothing but String whitespace, which the empty text does. */
    public static boolean isBlank(String text) {
        return text.codePoints().allMatch(StringWhitespace::isWhitespace);
    }
}
