package souther.lsp.protocol;

import souther.compiler.fmt.Skeleton;

/**
 * A declaration written for a client, either way it can read one.
 *
 * <p>Both are written from the one skeleton the analyzer built, so what a client without
 * placeholders inserts is exactly what a client with them inserts if every placeholder is left as it
 * stands. Two spellings of one declaration would agree until either moved.
 *
 * <p>A client says whether it reads placeholders, and one that says nothing has said no — the
 * protocol's own default, and the reason this cannot be assumed. What such a client is sent has no
 * {@code insertTextFormat} at all: the field is what says the text is to be read as a snippet, and a
 * text with {@code ${1:name}} in it and nothing saying so lands in the buffer as those characters.
 */
public final class Insertion {

    private Insertion() {}

    /** The LSP {@code InsertTextFormat} for a snippet. */
    public static final int SNIPPET_FORMAT = 2;

    /** The declaration as it stands, holes and all — for a client that does not read placeholders. */
    public static String plain(Skeleton.Built written) {
        return written.text();
    }

    /**
     * The same, with each hole marked as a place to tab to, numbered in the order they are written.
     *
     * <p>The characters the snippet grammar reads — {@code $}, {@code }} and the backslash that
     * escapes them — are escaped wherever they stand in the declaration, inside a hole as much as
     * outside one. None of them can be written by a skeleton today; escaping them anyway is what
     * makes that a fact about this text rather than something to remember when the next hole is
     * filled from something an author wrote.
     */
    public static String snippet(Skeleton.Built written) {
        StringBuilder out = new StringBuilder();
        int at = 0;
        int number = 0;
        for (Skeleton.Placed hole : written.holes()) {
            escaped(out, written.text().substring(at, hole.start()));
            out.append("${").append(++number).append(':');
            escaped(out, written.text().substring(hole.start(), hole.end()));
            out.append('}');
            at = hole.end();
        }
        escaped(out, written.text().substring(at));
        return out.toString();
    }

    private static void escaped(StringBuilder out, String text) {
        for (int i = 0; i < text.length(); i++) {
            char c = text.charAt(i);
            if (c == '$' || c == '}' || c == '\\') {
                out.append('\\');
            }
            out.append(c);
        }
    }
}
