package souther.compiler.doc;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Which lines of a document are inside a block whose text is taken as it stands.
 *
 * <p>A document says where its own structure is written, and inside such a block it says the
 * opposite: a {@code ## Example input} in a fenced sample is the sample, not a heading, and a
 * declaration written in one is what the sample looks like, not a name to publish. Every reader of
 * a document's structure asks here first, so there is one account of it rather than one per reader.
 *
 * <p>What opens a block is remembered, and only what closes that block closes it. A boolean would
 * have {@code ....} inside an AsciiDoc {@code ----} listing end it, and a {@code ~~~} inside a
 * markdown fence end that — after which every blank line and every heading in the rest of the block
 * reads as somewhere a document may be cut or a section may begin.
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

    /** For each line, whether it is inside such a block or is one of the lines delimiting it. */
    static boolean[] lines(String[] lines) {
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
            if (DELIMITED.matcher(line).matches()) {
                delimited = line;
                opaque[i] = true;
                continue;
            }
            Matcher opening = FENCED.matcher(line);
            if (opening.matches()) {
                fenced = opening.group(1).charAt(0);
                fence = opening.group(1).length();
                opaque[i] = true;
            }
        }
        return opaque;
    }
}
