package souther.compiler.doc;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Which lines of a document are inside a block whose text is taken as it stands.
 *
 * <p>A document says where its own structure is written, and inside such a block it says the
 * opposite: a {@code ## Example input} in a fenced sample is the sample, not a heading, and a
 * declaration written in one is what the sample looks like, not a name to publish. Every reader of
 * a document's structure asks here, so there is one account of it rather than one per reader.
 *
 * <p>One account, not one grammar. What delimits such a block is the document's own notation, and
 * the two notations disagree about the same line: {@code ----} opens a listing in AsciiDoc and is a
 * thematic break in markdown, so reading a markdown file by AsciiDoc's rules turns the rest of it
 * opaque and every name it goes on to declare disappears. A caller says which document it is
 * holding.
 *
 * <p>What opens a block is remembered, and only what closes that block closes it. A boolean would
 * have {@code ....} inside an AsciiDoc {@code ----} listing end it, and a {@code ~~~} inside a
 * markdown fence end that — after which every blank line and every heading in the rest of the
 * block reads as somewhere a document may be cut or a section may begin.
 */
final class TakenAsItStands {

    /**
     * An AsciiDoc block delimiter: four or more of one of these repeated, alone on the line —
     * listing, literal, passthrough, and the comment block. It is closed by the same line.
     */
    private static final Pattern DELIMITED = Pattern.compile("^([-.+/])\\1{3,}$");

    /**
     * A markdown fence: three or more backticks or tildes, and after them the info string naming
     * what is inside. It is closed by a run of the same character, at least as long, with nothing
     * after it — an info string is how a fence opens, so a line carrying one never closes one.
     */
    private static final Pattern FENCED = Pattern.compile("^(`{3,}|~{3,})(.*)$");

    private TakenAsItStands() {}

    /** For each line of an AsciiDoc document, whether its text is taken as it stands. */
    static boolean[] asciiDoc(String[] lines) {
        return lines(lines, true, false);
    }

    /** For each line of a markdown document, the same question in markdown's notation. */
    static boolean[] markdown(String[] lines) {
        return lines(lines, false, true);
    }

    /**
     * The same question asked of a document without being told which notation it is written in.
     *
     * <p>Only a reader choosing where to cut a long answer asks this way, and it is answered by
     * either notation delimiting a block. Reading a markdown thematic break as opening a listing
     * costs that reader some of the places it would rather stop, and it is left with the end of a
     * line and the count, which is what bounds the answer in the first place. A reader deciding
     * what a document declares cannot be wrong that way, and does not ask this.
     */
    static boolean[] either(String[] lines) {
        return lines(lines, true, true);
    }

    private static boolean[] lines(String[] lines, boolean delimits, boolean fences) {
        boolean[] opaque = new boolean[lines.length];
        String delimited = null;
        char fenced = 0;
        int fence = 0;
        for (int i = 0; i < lines.length; i++) {
            String line = lines[i].strip();
            if (delimited != null) {
                opaque[i] = true;
                if (line.equals(delimited)) {
                    delimited = null;
                }
                continue;
            }
            if (fenced != 0) {
                opaque[i] = true;
                Matcher closing = FENCED.matcher(line);
                if (closing.matches() && closing.group(1).charAt(0) == fenced
                        && closing.group(1).length() >= fence && closing.group(2).isBlank()) {
                    fenced = 0;
                }
                continue;
            }
            if (delimits && DELIMITED.matcher(line).matches()) {
                delimited = line;
                opaque[i] = true;
                continue;
            }
            Matcher opening = fences ? FENCED.matcher(line) : null;
            if (opening != null && opening.matches()) {
                fenced = opening.group(1).charAt(0);
                fence = opening.group(1).length();
                opaque[i] = true;
            }
        }
        return opaque;
    }
}
