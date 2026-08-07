package souther.compiler.doc;

import java.nio.charset.StandardCharsets;
import java.util.Base64;
import java.util.regex.Pattern;

/**
 * One answer's worth of a document, and where the next one starts.
 *
 * <p>A name being addressable says a reader can ask for a smaller thing; it does not bound what
 * comes back for the larger one. The specification's sections are named one by one and
 * {@code compile-errors} is still every diagnostic there is, because a section's body runs on
 * through its subsections. So how much a caller is handed at once is a question the transport
 * answers, separately from what the documents are named.
 *
 * <p>Where an answer is cut is chosen from the document rather than from the count: a heading if
 * there is one, failing that a blank line, failing that the end of a line. None of them is inside a
 * block the document says is taken as it stands, because half a code fence is not text a reader can
 * act on. The count is what makes the cut necessary, not what decides where it falls.
 *
 * <p>The cursor is the server's own to read. It carries where to resume and what it was measured
 * against, so a document that changed underneath — a jar bundling a different library's docs —
 * is a cursor refused rather than an answer resumed in the wrong place. A caller that reads a byte
 * position out of it and does arithmetic on it is writing against something that is not published;
 * what is published is that a cursor comes back and goes out again unread.
 */
final class Continuation {

    /**
     * How much of a document one answer carries.
     *
     * <p>Above every answer the other tools give whole — a jar's largest class, the standard
     * library's longest module, the listing of every name there is — so an answer that is cut is
     * never cut smaller than what this server already hands over in one piece. Of the names
     * {@code doc_read} answers, fourteen of three hundred and six are over it.
     */
    private static final int MOST = 16_000;

    /** A heading: a markdown one, or a specification one as the section listing writes them. */
    private static final Pattern HEADING = Pattern.compile("^(#{1,6}|={2,})\\s+\\S.*$");

    /** An AsciiDoc attribute line — the anchor a heading is asked for by, and its further names. */
    private static final Pattern ATTRIBUTE = Pattern.compile("^\\[[^]]*]\\s*$");

    /**
     * A delimiter opening or closing a block whose text is taken as it stands: a markdown fence, and
     * the AsciiDoc listing, literal, passthrough and comment blocks. Inside one, a blank line is
     * content and a {@code ####} is not a heading, so neither is a place to stop.
     */
    private static final Pattern OPAQUE_DELIMITER =
            Pattern.compile("^(```|~~~).*$|^([-.+/])\\2{3,}$");

    /** What a cursor is written as, so a client cannot spend a call learning it by hand. */
    static final String SPELLED = "^[A-Za-z0-9_-]+$";

    private Continuation() {}

    /** An answer that fits, and null for {@code cursor} when there is nothing after it. */
    record Part(String text, String cursor, int remaining) {}

    /**
     * The part of {@code text} that {@code cursor} asks for, or the first part when it is null.
     *
     * @throws IllegalArgumentException when the cursor was not measured against this text
     */
    static Part of(String text, String cursor) {
        int from = cursor == null ? 0 : resume(text, cursor);
        if (text.length() - from <= MOST) {
            return new Part(text.substring(from), null, 0);
        }
        int to = cut(text, from);
        return new Part(text.substring(from, to), cursorAt(text, to), text.length() - to);
    }

    /** Where the answer starting at {@code from} ends: the last place the document offers. */
    private static int cut(String text, int from) {
        int at = from;
        int heading = -1;
        int blank = -1;
        int attributes = -1;
        boolean opaque = false;
        while (at < text.length() && at - from <= MOST) {
            int end = text.indexOf('\n', at);
            String line = end < 0 ? text.substring(at) : text.substring(at, end);
            if (OPAQUE_DELIMITER.matcher(line).matches()) {
                opaque = !opaque;
                attributes = -1;
            } else if (opaque) {
                attributes = -1;
            } else {
                // The attribute lines above a heading are the heading's, so a part that stops at
                // the heading stops before them. Left behind, they end one answer with the name of
                // something that is not in it.
                if (ATTRIBUTE.matcher(line).matches()) {
                    attributes = attributes < 0 ? at : attributes;
                } else if (HEADING.matcher(line).matches()) {
                    heading = Math.max(attributes < 0 ? at : attributes, heading);
                    attributes = -1;
                } else {
                    attributes = -1;
                    if (line.isBlank()) {
                        blank = at;
                    }
                }
            }
            if (end < 0) {
                break;
            }
            at = end + 1;
        }
        if (heading > from) {
            return heading;
        }
        if (blank > from) {
            return blank;
        }
        // One line longer than the count allows, and nowhere in it the document says to stop.
        return at > from ? Math.min(at, text.length()) : Math.min(from + MOST, text.length());
    }

    /**
     * The cursor for resuming at {@code at}.
     *
     * <p>What it was measured against travels with it. The alternative is trusting a position
     * against text nobody checked is the same text, which reads the middle of one document at an
     * offset taken from another.
     */
    private static String cursorAt(String text, int at) {
        return Base64.getUrlEncoder().withoutPadding().encodeToString(
                (at + "." + text.length() + "." + text.hashCode()).getBytes(StandardCharsets.UTF_8));
    }

    private static int resume(String text, String cursor) {
        String[] written;
        try {
            written = new String(Base64.getUrlDecoder().decode(cursor), StandardCharsets.UTF_8)
                    .split("\\.");
        } catch (IllegalArgumentException e) {
            throw new IllegalArgumentException(stale());
        }
        if (written.length != 3) {
            throw new IllegalArgumentException(stale());
        }
        try {
            if (Integer.parseInt(written[1]) != text.length()
                    || Integer.parseInt(written[2]) != text.hashCode()) {
                throw new IllegalArgumentException(stale());
            }
            int at = Integer.parseInt(written[0]);
            if (at < 0 || at > text.length()) {
                throw new IllegalArgumentException(stale());
            }
            return at;
        } catch (NumberFormatException e) {
            throw new IllegalArgumentException(stale());
        }
    }

    private static String stale() {
        return "this `cursor` was not measured against this answer — ask again without one,"
                + " and carry the `cursor` that answer comes back with";
    }
}
