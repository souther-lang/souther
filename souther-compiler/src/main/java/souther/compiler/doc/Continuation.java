package souther.compiler.doc;

import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.Base64;
import java.util.HexFormat;
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
 * <p>The count is the guarantee, and where the cut falls is the preference. A heading is preferred,
 * failing that a blank line, failing that the end of a line, and failing that the count itself. The
 * first two are only taken outside a block whose text is taken as it stands, since half a code
 * fence is not text a reader can act on and a blank line inside one is content. But a single line
 * or a single block may be longer than one answer carries, and then there is no boundary left to
 * prefer: the answer is cut where the count runs out. Keeping the block whole instead would be a
 * bound a document could talk this server out of by writing a long enough fence.
 *
 * <p>The cursor is the server's own to read. It carries where to resume and a digest of what it was
 * measured against, so a document that changed underneath — a jar bundling a different library's
 * docs — is a cursor refused rather than an answer resumed in the wrong place. A caller that reads
 * a position out of it and does arithmetic on it is writing against something that is not
 * published; what is published is that a cursor comes back and goes out again unread.
 */
final class Continuation {

    /**
     * How much of a document one answer carries, the whole answer counted.
     *
     * <p>Above every answer the other tools give whole — a jar's largest class, the standard
     * library's longest module, the listing of every name there is — so an answer that is cut is
     * never cut smaller than what this server already hands over in one piece.
     *
     * <p>What a part says about carrying on is part of that answer and comes out of this, so the
     * caller passes what is left once that line is written rather than this.
     */
    static final int MOST = 16_000;

    /** A heading: a markdown one, or a specification one as the section listing writes them. */
    private static final Pattern HEADING = Pattern.compile("^(#{1,6}|={2,})\\s+\\S.*$");

    /** An AsciiDoc attribute line — the anchor a heading is asked for by, and its further names. */
    private static final Pattern ATTRIBUTE = Pattern.compile("^\\[[^]]*]\\s*$");

    /** What a cursor is written as, so a client cannot spend a call learning it by hand. */
    static final String SPELLED = "^[A-Za-z0-9_-]+$";

    /** How many bytes of the digest travel, which is what two answers would have to collide on. */
    private static final int DIGEST = 8;

    private Continuation() {}

    /** An answer that fits, and null for {@code cursor} when there is nothing after it. */
    record Part(String text, String cursor, int remaining) {}

    /**
     * The part of {@code text} that {@code cursor} asks for, or the first part when it is null,
     * carrying at most {@code budget} characters.
     *
     * @throws IllegalArgumentException when the cursor was not measured against this text
     */
    static Part of(String text, String cursor, int budget) {
        int from = cursor == null ? 0 : resume(text, cursor);
        if (text.length() - from <= budget) {
            return new Part(text.substring(from), null, 0);
        }
        int to = cut(text, from, budget);
        return new Part(text.substring(from, to), cursorAt(text, to), text.length() - to);
    }

    /**
     * Where the answer starting at {@code from} ends.
     *
     * <p>Never past {@code from + budget}: every candidate is a position the walk reached while
     * still inside the count, and what is answered when there is no candidate is the count itself.
     */
    private static int cut(String text, int from, int budget) {
        int limit = Math.min(from + budget, text.length());
        String[] lines = text.split("\n", -1);
        boolean[] opaque = TakenAsItStands.lines(lines);
        int heading = -1;
        int blank = -1;
        int attributes = -1;
        int line = -1;
        int at = 0;
        for (int i = 0; i < lines.length && at <= limit; i++) {
            if (at > from) {
                line = at;
                if (opaque[i]) {
                    attributes = -1;
                } else if (ATTRIBUTE.matcher(lines[i]).matches()) {
                    // The attribute lines above a heading are the heading's, so a part that stops
                    // at the heading stops before them. Left behind, they end one answer with the
                    // name of something that is not in it.
                    attributes = attributes < 0 ? at : attributes;
                } else if (HEADING.matcher(lines[i]).matches()) {
                    heading = Math.max(attributes < 0 ? at : attributes, heading);
                    attributes = -1;
                } else {
                    attributes = -1;
                    if (lines[i].isBlank()) {
                        blank = at;
                    }
                }
            }
            at += lines[i].length() + 1;
        }
        if (heading > from) {
            return heading;
        }
        // A heading is where the document itself starts something new, and a part that stops there
        // is worth a short part before it. A blank line and the end of a line are not that; they
        // are only places nothing is being cut through. Taking one that carries almost none of the
        // count spends a whole call on a few characters, which is what a document with a block or a
        // line longer than an answer carries would otherwise make this server do repeatedly. Below
        // half the count they lose to cutting where the count runs out.
        int enough = from + budget / 2;
        if (blank >= enough) {
            return blank;
        }
        if (line >= enough) {
            return line;
        }
        return limit;
    }

    /**
     * The cursor for resuming at {@code at}.
     *
     * <p>What it was measured against travels with it. The alternative is trusting a position
     * against text nobody checked is the same text, which reads the middle of one document at an
     * offset taken from another.
     */
    private static String cursorAt(String text, int at) {
        return Base64.getUrlEncoder().withoutPadding()
                .encodeToString((at + "." + digest(text)).getBytes(StandardCharsets.UTF_8));
    }

    private static int resume(String text, String cursor) {
        String[] written;
        try {
            written = new String(Base64.getUrlDecoder().decode(cursor), StandardCharsets.UTF_8)
                    .split("\\.");
        } catch (IllegalArgumentException e) {
            throw new IllegalArgumentException(stale());
        }
        if (written.length != 2 || !written[1].equals(digest(text))) {
            throw new IllegalArgumentException(stale());
        }
        try {
            int at = Integer.parseInt(written[0]);
            if (at < 0 || at > text.length()) {
                throw new IllegalArgumentException(stale());
            }
            return at;
        } catch (NumberFormatException e) {
            throw new IllegalArgumentException(stale());
        }
    }

    /** What identifies the answer a cursor was measured against. */
    private static String digest(String text) {
        try {
            byte[] sum = MessageDigest.getInstance("SHA-256")
                    .digest(text.getBytes(StandardCharsets.UTF_8));
            return HexFormat.of().formatHex(sum, 0, DIGEST);
        } catch (NoSuchAlgorithmException e) {
            throw new IllegalStateException(e);
        }
    }

    private static String stale() {
        return "this `cursor` was not measured against this answer — ask again without one,"
                + " and carry the `cursor` that answer comes back with";
    }
}
