package souther.compiler.diag;

import souther.compiler.diag.msg.FindingRegion;
import souther.compiler.diag.msg.Message;

/**
 * A secondary source region with a note. Used when one error points at more than one place — the
 * left behavior's output and the right behavior's input of a failed composition, or the two
 * branches of an {@code if} that disagree. {@code said} is what the label says, and carries the
 * values it names.
 *
 * <p>{@code sourceId} names the source this region is in, and is null only where nothing knows it:
 * a region built from a hand-made position, whose file is then the diagnostic's own. A problem
 * written in two files — a stand-in in one and the row it contradicts in another — names the second,
 * so the renderer quotes the right text rather than the line that happens to sit at that number in
 * the first. Read it through {@link #sourceIdOr(String)}: a resolver is asked about a source that is
 * named, never about null.
 */
public record LabeledRegion(Region region, String sourceId, Message said) {

    public LabeledRegion {
        java.util.Objects.requireNonNull(said, "a secondary region says why it is pointed at");
        // Two things can say which file this is in — what the label was given, and what the region's
        // own position was read from — and they may not disagree: saying two different files is a
        // disagreement no reader can resolve, and is exactly the shape of mistake that put a
        // diagnostic's coordinates and its file name in different files to begin with.
        if (sourceId != null && region != null && region.start() != null
                && region.start().sourceId() != null
                && !sourceId.equals(region.start().sourceId())) {
            throw new IllegalArgumentException("a label in " + sourceId
                    + " points at a region read from " + region.start().sourceId());
        }
        // Where only the region knows, that is the answer. A caller holding a region read off a
        // source holds the file it came from as part of it, and a label that dropped it left the
        // renderer to fall back on the diagnostic's own — which quotes another file's line at the
        // same numbers. The two are one fact, so this does not leave a caller a way to carry half.
        if (sourceId == null && region != null && region.start() != null) {
            sourceId = region.start().sourceId();
        }
    }

    /** The source this region is in, inheriting {@code diagnosticSourceId} when it names none. */
    public String sourceIdOr(String diagnosticSourceId) {
        return sourceId == null ? diagnosticSourceId : sourceId;
    }

    /**
     * Whether the diagnostic finds this region wrong too, rather than showing it so that a reader
     * can see why the primary is — which is what the label says ({@link FindingRegion}), and is read
     * off nothing else.
     *
     * <p>What reads it is the decision about which files a report is said in. A report is said
     * wherever it is written, so an author editing any of those files is told; the rule a subject
     * was judged against is not one of those files, however necessary reading it is.
     */
    public boolean belongsToFinding() {
        return said instanceof FindingRegion;
    }
}
