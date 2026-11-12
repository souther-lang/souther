package souther.compiler.cst;

/**
 * The white space between the tokens of a source: a space, a tab, a carriage return or a line
 * feed, and nothing else.
 *
 * <p>Not Unicode's white space, nor Java's. A source is laid out in these four, and any other code
 * point between tokens is one more token ({@link CstLexer}); within a comment it is part of what
 * the comment says. So whatever reads a source's layout — the lexer, the formatter, a report that
 * quotes a source's lines — asks this, and what it takes for the space around a token is what the
 * lexer reads as that.
 */
public final class SourceSpace {

    private SourceSpace() {}

    /** Whether {@code c} is white space between tokens. */
    public static boolean is(int c) {
        return c == ' ' || c == '\t' || c == '\r' || c == '\n';
    }

    /** Whether {@code text} is nothing but white space between tokens, or nothing. */
    public static boolean isBlank(CharSequence text) {
        return text.chars().allMatch(SourceSpace::is);
    }

    /** {@code text} without the white space between tokens it begins with. */
    public static String stripLeading(String text) {
        int from = 0;
        while (from < text.length() && is(text.charAt(from))) {
            from++;
        }
        return text.substring(from);
    }

    /** {@code text} without the white space between tokens it ends with. */
    public static String stripTrailing(String text) {
        int to = text.length();
        while (to > 0 && is(text.charAt(to - 1))) {
            to--;
        }
        return text.substring(0, to);
    }

    /** {@code text} without the white space between tokens it begins or ends with. */
    public static String strip(String text) {
        return stripTrailing(stripLeading(text));
    }
}
