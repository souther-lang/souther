package souther.compiler.diag.msg;

import java.util.ArrayList;
import java.util.List;

/**
 * A catalog entry as its literal text and the values it names, parsed once.
 *
 * <p>What reads an entry and what checks one are the same parser. Written twice they drift, which is
 * the defect this whole area exists to remove: a renderer that took {@code {} } to the next brace and
 * a check that only recognised {@code {[a-zA-Z][a-zA-Z0-9]*}} disagreed about {@code {held_by}} and
 * about an unclosed {@code {field}, so an entry naming a value nothing fills passed the build and
 * showed the reader a brace.
 */
public record MessageTemplate(List<Part> parts) {

    /** A run of literal text, or a value the entry names. */
    public sealed interface Part {
        record Text(String written) implements Part {}

        record Value(String name) implements Part {}

        /** A brace the entry opens and does not close, or closes with nothing between. */
        record Malformed(String written, String why) implements Part {}
    }

    /** The names this entry writes, in the order it writes them. */
    public List<String> names() {
        List<String> named = new ArrayList<>();
        for (Part part : parts) {
            if (part instanceof Part.Value value) {
                named.add(value.name());
            }
        }
        return named;
    }

    /** What is wrong with this entry as an entry, empty when nothing is. */
    public List<String> malformations() {
        List<String> found = new ArrayList<>();
        for (Part part : parts) {
            if (part instanceof Part.Malformed bad) {
                found.add(bad.why() + ": " + bad.written());
            }
        }
        return found;
    }

    /**
     * {@code written} as its parts.
     *
     * <p>A name is a Java identifier, because it is a record component's name. Anything else between
     * braces is malformed rather than literal text: an entry that meant a brace and an entry that
     * misspelled a value look the same to a reader, and the second is the one worth failing on. An
     * entry that means a brace writes it twice.
     */
    public static MessageTemplate parse(String written) {
        List<Part> parts = new ArrayList<>();
        int at = 0;
        StringBuilder text = new StringBuilder();
        while (at < written.length()) {
            char c = written.charAt(at);
            // A brace of its own is written twice. An entry filled by name has no quoting to undo,
            // so this is the one place a brace can be said to be itself — and the parser that reads
            // an entry and the check that holds it to naming values read it the same way.
            if ((c == '{' || c == '}') && at + 1 < written.length()
                    && written.charAt(at + 1) == c) {
                text.append(c);
                at += 2;
                continue;
            }
            if (c != '{') {
                text.append(c);
                at++;
                continue;
            }
            int close = written.indexOf('}', at);
            if (close < 0) {
                flush(text, parts);
                parts.add(new Part.Malformed(written.substring(at), "a brace nothing closes"));
                return new MessageTemplate(List.copyOf(parts));
            }
            String named = written.substring(at + 1, close);
            flush(text, parts);
            parts.add(isAName(named) ? new Part.Value(named)
                    : new Part.Malformed(written.substring(at, close + 1),
                            "a brace holding something that is not a value's name"));
            at = close + 1;
        }
        flush(text, parts);
        return new MessageTemplate(List.copyOf(parts));
    }

    private static void flush(StringBuilder text, List<Part> parts) {
        if (!text.isEmpty()) {
            parts.add(new Part.Text(text.toString()));
            text.setLength(0);
        }
    }

    private static boolean isAName(String written) {
        if (written.isEmpty() || !Character.isJavaIdentifierStart(written.charAt(0))) {
            return false;
        }
        for (int i = 1; i < written.length(); i++) {
            if (!Character.isJavaIdentifierPart(written.charAt(i))) {
                return false;
            }
        }
        return true;
    }
}
