package souther.compiler.diag;

import souther.compiler.diag.msg.Message;

/**
 * One place a diagnostic points at, with the source it is in resolved. A {@link Diagnostic} says
 * where its primary region is and what its secondaries say, but which file each of those is in is
 * settled outside it — so a reader has to be handed both to know what text to quote. A spot is that
 * pairing, made once.
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

    /** A secondary region, in its own source or the diagnostic's when it names none. */
    public static Spot secondary(LabeledRegion label, String diagnosticSourceId) {
        return new Spot(label.sourceIdOr(diagnosticSourceId), label.region(), label.said());
    }

    /** Whether this spot carries a note — false for the primary region. */
    public boolean labelled() {
        return said != null;
    }
}
