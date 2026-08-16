package souther.compiler.diag;

import java.util.Objects;

/**
 * What a diagnostic points at: a stretch of text, or nothing to point at and where the code is
 * instead.
 *
 * <p>A {@link Citation} tells five states apart, and this is the boundary it was being flattened at.
 * A finding about code inside a module's published text is a citation that has no place and does know
 * which module the code is in; handed to a diagnostic as a region it did not have, that became a
 * region of {@code null} — which says neither, and left the anchoring to work the provenance out
 * again from whichever module the report was filed under. That is the inference this change removes,
 * arriving one boundary later.
 *
 * <p>So the value that could not be carried is carried. {@link Unavailable} is not the absence of a
 * primary: it is a report that knows what to tell a reader and has nowhere to send them, which is
 * exactly what {@link DiagnosticPlace.Unavailable} is for a label.
 *
 * <p>Not {@link DiagnosticPlace} itself, and not yet. That type holds a region to being a place a
 * reader can be sent to, and a primary region is not held to anything — over one compile of this
 * suite 53 of 3545 name no source while saying the code is written there. Classifying them is the
 * open question about whether such a region is a place at all, and this leaves it open: what a pass
 * built arrives here as {@link AtARegion} and is passed on unread.
 *
 * <p>A diagnostic may still have none of either, which is a third thing and is null for now — the
 * same open question, at its other end.
 */
public sealed interface Primary {

    /**
     * A stretch of text a pass built the report at, as it built it.
     *
     * <p>Unclassified on purpose. Whether a reader can be sent there is a question this does not
     * ask, because the answer for some of them is no and nothing has decided what to do about that.
     */
    record AtARegion(Region region) implements Primary {

        public AtARegion {
            Objects.requireNonNull(region, "a report about a region has one");
        }
    }

    /**
     * Nowhere to point, and the code is written in {@code from}.
     *
     * <p>What a report about code inside a module's published text has: the position it was found at
     * is a line of a text no reader holds, so there is nothing to offer, and which module wrote that
     * code is known and is what a reader is told instead.
     */
    record Unavailable(SourceProvenance from) implements Primary {

        public Unavailable {
            Objects.requireNonNull(from, "code out of sight came from somewhere");
        }
    }

    /** The region this points at, or null where there is nothing to point at. What every surface
     *  reading a primary region already asked for, answered the same way — a report with nowhere to
     *  point has no region, and now it also has what to say. */
    static Region regionOf(Primary primary) {
        return primary instanceof AtARegion(Region region) ? region : null;
    }
}
