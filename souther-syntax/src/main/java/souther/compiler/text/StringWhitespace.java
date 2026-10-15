package souther.compiler.text;

import net.unit8.notation199x.WhiteSpace;

/**
 * String whitespace (spec §string-whitespace) as the syntax reads it, for a rule of the grammar that
 * asks whether a string literal holds anything but whitespace.
 *
 * <p>The set is {@link WhiteSpace}, which is the one the runtime's {@code trim} and {@code words}
 * scan by, so the grammar and a running program cannot disagree on it.
 */
public final class StringWhitespace {

    private StringWhitespace() {}

    /** Whether {@code text} holds nothing but String whitespace, which the empty text does. */
    public static boolean isBlank(String text) {
        return text.codePoints().allMatch(WhiteSpace::contains);
    }
}
