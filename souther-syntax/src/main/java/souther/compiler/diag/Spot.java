package souther.compiler.diag;

import souther.compiler.diag.msg.Supporting;

/**
 * One place a diagnostic points at, with the source it is in resolved. A {@link Diagnostic} says
 * where its primary region is and what its secondaries say, but which file each of those is in is
 * settled outside it — so a reader has to be handed both to know what text to quote. A spot is that
 * pairing, made once.
 *
 * <p>{@code said} is null for the primary region, which has no note of its own: what it points at is
 * what the message is about.
 */
public record Spot(String sourceId, Region region, Supporting said) {

    /** The primary region of {@code d}, in {@code sourceId}. */
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
