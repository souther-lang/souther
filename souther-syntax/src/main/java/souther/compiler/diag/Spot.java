package souther.compiler.diag;

import souther.compiler.source.SourceId;

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
 * <p>A primary is told, and a secondary is not. Which is not because the two are different kinds of
 * place: it is because a primary region is not held to being one. A secondary goes through
 * {@link DiagnosticPlace}, so it names a source by construction; a primary does not, and over one
 * compile of this suite 53 of 3545 diagnostics carried a primary region that names no source while
 * saying the code is written at it, with another 22 carrying no region at all. For those, what this
 * is told is the only answer there is, and it comes from where the report was filed rather than from
 * the place — so a reader is sent to a file the numbers may not be of.
 *
 * <p>So this pairing is not the defect the rest of this package closed, and it is not settled
 * either. The rule those values keep is that a place answering for a source is not asked twice; here
 * the place does not always answer. What the field means where it does — the source the region is
 * in, or the file this report is being read from — is what has to be decided before it can be given
 * a type, and deciding it means reading what those diagnostics are about.
 *
 * <p>Every spot is somewhere. A label with nothing to quote is not one — it is
 * {@link DiagnosticPlace.Unavailable}, and a reader is told where the code came from rather than
 * sent anywhere ({@link DiagnosticView#unquotable()}).
 *
 * <p>{@link #said()} is null for the primary region, which has no note of its own: what it points at
 * is what the message is about.
 */
public final class Spot {

    private final SourceId sourceId;
    private final Region region;
    private final Message said;

    private Spot(SourceId sourceId, Region region, Message said) {
        this.sourceId = sourceId;
        this.region = region;
        this.said = said;
    }

    /** The primary region of {@code d}, in {@code sourceId} — which the caller says, holding the
     *  files, and which is none for a compile that names none. */
    public static Spot primary(Diagnostic d, SourceId sourceId) {
        return new Spot(sourceId, d.region(), null);
    }

    /** A second place, in the source its own place names. */
    public static Spot secondary(DiagnosticPlace.InSource place, Message said) {
        Objects.requireNonNull(place, "a second place a reader is sent to is somewhere");
        return new Spot(place.source(), place.region(),
                Objects.requireNonNull(said, "a second place says why it is pointed at"));
    }

    /** The source this is in, or none where a compile of one file named none. */
    public SourceId sourceId() {
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
