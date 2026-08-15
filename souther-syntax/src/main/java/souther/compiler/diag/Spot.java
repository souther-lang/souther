package souther.compiler.diag;

import souther.compiler.diag.msg.Message;

import java.util.Objects;

/**
 * One place a diagnostic points at, in the source it is in. A {@link Diagnostic} says where its
 * primary region is and what its secondaries say, and a reader has to be handed both the region and
 * its file to know what text to quote. A spot is that pairing, made once.
 *
 * <p>Made two ways, and there is no constructor that takes a source and a region separately.
 *
 * <p>A secondary reads its source off its place ({@link DiagnosticPlace.InSource}), which is where
 * that answer already is. What a renderer does with a spot is take the two apart again — the file to
 * quote from, the numbers to quote at — so a pair that could disagree is a marker put in one file
 * with its line read from another. That is the defect this whole change is about, and it does not
 * stop being it one layer downstream of where it was closed.
 *
 * <p>A primary is told, and its source is not the region's. What a caller is quoting from is the
 * caller's answer: a compile of one file hides source ids altogether and names none, and a view
 * built on the region's would be about a file that caller never speaks of. Whoever hands this a name
 * is the one holding the files, and what it has to hand over is where the primary region is — which
 * is what {@link Located} carries.
 *
 * <p>Every spot is somewhere. A label with nothing to quote is not one — it is
 * {@link DiagnosticPlace.Unavailable}, and a reader is told where the code came from rather than
 * sent anywhere ({@link DiagnosticView#unquotable()}).
 *
 * <p>{@link #said()} is null for the primary region, which has no note of its own: what it points at
 * is what the message is about.
 */
public final class Spot {

    private final String sourceId;
    private final Region region;
    private final Message said;

    private Spot(String sourceId, Region region, Message said) {
        this.sourceId = sourceId;
        this.region = region;
        this.said = said;
    }

    /** The primary region of {@code d}, in {@code sourceId} — which the caller says, holding the
     *  files, and which is none for a compile that names none. */
    public static Spot primary(Diagnostic d, String sourceId) {
        return new Spot(sourceId, d.region(), null);
    }

    /** A second place, in the source its own place names. */
    public static Spot secondary(DiagnosticPlace.InSource place, Message said) {
        Objects.requireNonNull(place, "a second place a reader is sent to is somewhere");
        return new Spot(place.source(), place.region(),
                Objects.requireNonNull(said, "a second place says why it is pointed at"));
    }

    /** The source this is in, or none where a compile of one file named none. */
    public String sourceId() {
        return sourceId;
    }

    /** The stretch this points at. */
    public Region region() {
        return region;
    }

    /** What this says, or null for the primary region. */
    public Message said() {
        return said;
    }

    /** Whether this spot carries a note — false for the primary region. */
    public boolean labelled() {
        return said != null;
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof Spot that && Objects.equals(sourceId, that.sourceId)
                && Objects.equals(region, that.region) && Objects.equals(said, that.said);
    }

    @Override
    public int hashCode() {
        return Objects.hash(sourceId, region, said);
    }

    @Override
    public String toString() {
        return "Spot[" + sourceId + " " + region + (said == null ? "" : " " + said) + "]";
    }
}
