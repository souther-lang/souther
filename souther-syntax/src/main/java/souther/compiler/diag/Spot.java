package souther.compiler.diag;

import souther.compiler.diag.msg.Message;

/**
 * One place a diagnostic points at, in the source it is in. A {@link Diagnostic} says where its
 * primary region is and what its secondaries say, and a reader has to be handed both the region and
 * its file to know what text to quote. A spot is that pairing, made once.
 *
 * <p>Every spot is somewhere. A label with nothing to quote is not one — it is
 * {@link DiagnosticPlace.Unavailable}, and a reader is told where the code came from rather than
 * sent anywhere ({@link DiagnosticView#unquotable()}).
 *
 * <p>{@code said} is null for the primary region, which has no note of its own: what it points at is
 * what the message is about.
 */
public record Spot(String sourceId, Region region, Message said) {

    /**
     * The primary region of {@code d}, in {@code sourceId}.
     *
     * <p>Told rather than read off the region, although the region carries a source of its own. What
     * a caller is quoting from is the caller's answer: a compile of one file hides source ids
     * altogether and names none, and a view built on the region's would be about a file that caller
     * never speaks of. Whoever hands this a name is the one holding the files, and what it has to
     * hand over is where the primary region is — which is what {@code Located} carries.
     */
    public static Spot primary(Diagnostic d, String sourceId) {
        return new Spot(sourceId, d.region(), null);
    }

    /** Whether this spot carries a note — false for the primary region. */
    public boolean labelled() {
        return said != null;
    }
}
