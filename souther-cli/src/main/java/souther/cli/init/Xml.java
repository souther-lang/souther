package souther.cli.init;

import java.util.ArrayList;
import java.util.List;

/**
 * Where an element ends in a document this command did not write.
 *
 * <p>Enough of XML to put a declaration inside the element it belongs in, and no more. A pom is
 * somebody's own file — its comments say why a version is what it is, and its layout is theirs — so
 * what goes back is the text they wrote with a block inserted into it, rather than a tree rendered
 * out again with the comments and the spacing gone.
 *
 * <p>The path is walked rather than the name searched for. A pom has {@code <plugins>} under
 * {@code <build>}, under {@code <pluginManagement>}, under {@code <reporting>} and under a profile,
 * and the first one a search finds is the wrong one about as often as it is the right one.
 */
final class Xml {

    private Xml() {}

    /**
     * Where the element at this path ends, or {@link #NOWHERE} where there is no such element.
     *
     * <p>Comments, CDATA, the declaration and a doctype are stepped over rather than read: a
     * {@code <plugins>} written inside a comment is not an element, and a document whose comment
     * mentions one would otherwise have a declaration inserted into its prose.
     */
    static int endOf(String xml, List<String> path) {
        List<String> open = new ArrayList<>();
        int at = 0;
        while (at < xml.length()) {
            int lt = xml.indexOf('<', at);
            if (lt < 0) {
                return NOWHERE;
            }
            if (xml.startsWith("<!--", lt)) {
                at = skipTo(xml, lt, "-->");
                continue;
            }
            if (xml.startsWith("<![CDATA[", lt)) {
                at = skipTo(xml, lt, "]]>");
                continue;
            }
            if (xml.startsWith("<?", lt)) {
                at = skipTo(xml, lt, "?>");
                continue;
            }
            if (xml.startsWith("<!", lt)) {
                at = skipTo(xml, lt, ">");
                continue;
            }
            int gt = endOfTag(xml, lt);
            if (gt < 0) {
                return NOWHERE;
            }
            String tag = xml.substring(lt + 1, gt).trim();
            if (tag.startsWith("/")) {
                // Asked before the path is: an end tag that closes something else is not the end of
                // the element being looked for, however deep the walk happens to be standing.
                if (!closes(open, tag)) {
                    return NOWHERE;   // not a document this can be walked down
                }
                if (open.equals(path)) {
                    return lt;
                }
                open.remove(open.size() - 1);
            } else if (!tag.endsWith("/")) {
                open.add(nameOf(tag));
            }
            at = gt + 1;
        }
        return NOWHERE;
    }

    /** What {@link #endOf} answers with where the document has no such element. */
    static final int NOWHERE = -1;

    /** Whether the document has an element at this path. */
    static boolean has(String xml, List<String> path) {
        return endOf(xml, path) != NOWHERE;
    }

    /**
     * What the first element at this path says, or null where the document has no such element.
     *
     * <p>The first and not every one: a coordinate is written once, and a document that writes a
     * second {@code <groupId>} somewhere below is writing about something else — a dependency, a
     * plugin — which is exactly what asking by path keeps out of the answer.
     */
    static String textOf(String xml, List<String> path) {
        List<String> open = new ArrayList<>();
        int content = -1;
        int at = 0;
        while (at < xml.length()) {
            int lt = xml.indexOf('<', at);
            if (lt < 0) {
                return null;
            }
            if (xml.startsWith("<!--", lt)) {
                at = skipTo(xml, lt, "-->");
                continue;
            }
            if (xml.startsWith("<![CDATA[", lt)) {
                at = skipTo(xml, lt, "]]>");
                continue;
            }
            if (xml.startsWith("<?", lt)) {
                at = skipTo(xml, lt, "?>");
                continue;
            }
            if (xml.startsWith("<!", lt)) {
                at = skipTo(xml, lt, ">");
                continue;
            }
            int gt = endOfTag(xml, lt);
            if (gt < 0) {
                return null;
            }
            String tag = xml.substring(lt + 1, gt).trim();
            if (tag.startsWith("/")) {
                if (!closes(open, tag)) {
                    return null;   // not a document this can be walked down
                }
                if (open.equals(path) && content >= 0) {
                    return xml.substring(content, lt).trim();
                }
                open.remove(open.size() - 1);
            } else if (!tag.endsWith("/")) {
                open.add(nameOf(tag));
                if (open.equals(path) && content < 0) {
                    content = gt + 1;
                }
            }
            at = gt + 1;
        }
        return null;
    }

    /**
     * The document with {@code block} written just inside the element at {@code path}, indented one
     * level under it.
     *
     * <p>The caller has established that the element is there. Indentation is taken from the
     * document rather than from a house style, so that what is inserted reads as part of the file it
     * lands in.
     */
    static String insertInto(String xml, List<String> path, String block) {
        int end = endOf(xml, path);
        String unit = unitOf(xml);
        int lineStart = xml.lastIndexOf('\n', end - 1) + 1;
        String before = xml.substring(lineStart, end);
        if (before.isBlank()) {
            return xml.substring(0, lineStart) + indent(block, before + unit, unit)
                    + xml.substring(lineStart);
        }
        // An end tag with something else on its line — `<plugins></plugins>`, or a document written
        // on one line. The block goes on lines of its own and the end tag follows it, indented as
        // its own line was.
        String outer = before.substring(0, before.length() - before.stripLeading().length());
        return xml.substring(0, end) + "\n" + indent(block, outer + unit, unit) + outer
                + xml.substring(end);
    }

    /**
     * {@code block} with every line indented by {@code indent}, and its last line ended.
     *
     * <p>The block's own nesting is restated in the document's unit rather than kept: a block
     * written here four spaces deep, dropped into a pom written two spaces deep, reads as text from
     * somewhere else. What is written in this file is four spaces per level, which is what is
     * translated.
     */
    static String indent(String block, String indent, String unit) {
        StringBuilder out = new StringBuilder();
        for (String line : block.stripTrailing().split("\n", -1)) {
            if (line.isBlank()) {
                out.append("\n");
                continue;
            }
            String body = line.stripLeading();
            int levels = (line.length() - body.length()) / WRITTEN_UNIT.length();
            out.append(indent).append(unit.repeat(levels)).append(body).append("\n");
        }
        return out.toString();
    }

    /** How deep one level is in the blocks this command writes, before they are restated. */
    private static final String WRITTEN_UNIT = "    ";

    /**
     * What one level of indentation is in this document.
     *
     * <p>Read off the first indented line rather than assumed, since a pom written with two spaces
     * and one written with four are both ordinary, and a block indented by the other one reads as
     * having been pasted in.
     */
    static String unitOf(String xml) {
        for (String line : xml.split("\n")) {
            String stripped = line.stripLeading();
            if (stripped.startsWith("<") && !stripped.startsWith("<?") && stripped.length()
                    < line.length()) {
                return line.substring(0, line.length() - stripped.length());
            }
        }
        return "    ";
    }

    /**
     * Whether this end tag closes the element that is open.
     *
     * <p>Asked rather than assumed. An end tag that closes something else — a stray one, a
     * misspelt one — leaves the walk one element up from where it thinks it is, and every path
     * asked about after it is answered about a different element. What that produced was a
     * declaration written outside the {@code <project>} it was meant to go inside, into a pom that
     * then parsed as nothing. A document this cannot follow is one this says it cannot follow.
     */
    private static boolean closes(List<String> open, String tag) {
        return !open.isEmpty() && open.get(open.size() - 1).equals(nameOf(tag.substring(1).trim()));
    }

    /** The name a start tag opens, without its attributes. */
    private static String nameOf(String tag) {
        int space = tag.length();
        for (int i = 0; i < tag.length(); i++) {
            if (Character.isWhitespace(tag.charAt(i))) {
                space = i;
                break;
            }
        }
        return tag.substring(0, space);
    }

    /** Where this tag ends, reading past a {@code >} that sits inside an attribute value. */
    private static int endOfTag(String xml, int lt) {
        char quote = 0;
        for (int i = lt + 1; i < xml.length(); i++) {
            char c = xml.charAt(i);
            if (quote != 0) {
                if (c == quote) {
                    quote = 0;
                }
            } else if (c == '"' || c == '\'') {
                quote = c;
            } else if (c == '>') {
                return i;
            }
        }
        return -1;
    }

    private static int skipTo(String xml, int from, String close) {
        int end = xml.indexOf(close, from);
        return end < 0 ? xml.length() : end + close.length();
    }

}
