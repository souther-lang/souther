package souther.compiler.doc;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * The parts of the syntax contract the specification includes, read into it where it includes them.
 *
 * <p>Each construct's section includes its own productions from {@code syntax/grammar.ebnf}, so a
 * form is written once, in the grammar, and shown where a reader of the construct meets it. A
 * renderer of the document resolves those includes itself; a reader that asks the bundled document
 * for a section is answered from this, which resolves them the same way before the document is cut
 * into sections, so what is answered is the grammar's text and not the directive naming it.
 *
 * <p>Only what the specification writes is read: an {@code include::} of a file under {@code
 * syntax/}, by one tagged region, optionally with {@code indent=0}. Any other include is refused
 * rather than passed through, because a directive left in the text would be answered as if it were
 * the specification's own words.
 */
final class SpecIncludes {

    private SpecIncludes() {}

    private static final Pattern INCLUDE = Pattern.compile("^include::([^\\[]*)\\[(.*)]\\s*$");
    private static final Pattern TAG = Pattern.compile("(?:^|,)tag=([a-z0-9-]+)(?:,|$)");
    private static final Pattern INDENT = Pattern.compile("(?:^|,)indent=0(?:,|$)");
    private static final Pattern MARKER = Pattern.compile("(?:tag|end)::[a-z0-9-]+\\[]");

    /**
     * {@code adoc} with every include replaced by the lines it names, each file read by
     * {@code read} from its path relative to the specification.
     */
    static String resolved(String adoc, Function<String, String> read) {
        String[] lines = adoc.split("\n", -1);
        List<String> out = new ArrayList<>();
        for (String line : lines) {
            Matcher include = INCLUDE.matcher(line);
            if (!include.matches()) {
                out.add(line);
                continue;
            }
            String path = include.group(1);
            String attributes = include.group(2);
            Matcher tag = TAG.matcher(attributes);
            if (!path.startsWith("syntax/") || !tag.find()) {
                throw new IllegalStateException("an include this document does not resolve: " + line);
            }
            List<String> region = region(read.apply(path), tag.group(1), path);
            out.addAll(INDENT.matcher(attributes).find() ? unindented(region) : region);
        }
        return String.join("\n", out);
    }

    /** The lines between {@code tag::name[]} and {@code end::name[]}, no line with a marker kept. */
    private static List<String> region(String text, String name, String path) {
        String opens = "tag::" + name + "[]";
        String closes = "end::" + name + "[]";
        List<String> out = new ArrayList<>();
        boolean inside = false;
        boolean found = false;
        for (String line : text.split("\n", -1)) {
            if (line.contains(opens)) {
                inside = true;
                found = true;
            } else if (line.contains(closes)) {
                inside = false;
            } else if (inside && !MARKER.matcher(line).find()) {
                out.add(line);
            }
        }
        if (!found) {
            throw new IllegalStateException(path + " has no region " + name);
        }
        return out;
    }

    /** The lines with the indentation they share taken off, as {@code indent=0} asks. */
    private static List<String> unindented(List<String> lines) {
        int common = Integer.MAX_VALUE;
        for (String line : lines) {
            if (!line.isBlank()) {
                common = Math.min(common, line.length() - line.stripLeading().length());
            }
        }
        if (common == Integer.MAX_VALUE) {
            return lines;
        }
        List<String> out = new ArrayList<>();
        for (String line : lines) {
            out.add(line.isBlank() ? "" : line.substring(common));
        }
        return out;
    }
}
