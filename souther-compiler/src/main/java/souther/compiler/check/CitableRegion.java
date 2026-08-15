package souther.compiler.check;

import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;

import java.util.Objects;
import java.util.Optional;

/**
 * A region a diagnostic may send a reader to: one read off a source this compile can quote.
 *
 * <p>Where a node was written and whether that place can be pointed at are separate questions. A
 * declaration read back out of a published module was written somewhere, and the region says a line
 * and a column of a text reassembled from what the module carries — numbers no reader holds a file
 * for. A label built over one of those names no source, and a renderer reading a label that names
 * none falls back on the diagnostic's own file, which quotes whatever happens to sit at those
 * numbers in the file the reader is looking at. So the question is asked before a label is made,
 * rather than left for the renderer to fail at.
 *
 * <p>Only the region. Which source it is in is part of the region already, and holding a second copy
 * beside it would be two values for one fact with nothing keeping them the same.
 */
record CitableRegion(Region region) {

    CitableRegion {
        Objects.requireNonNull(region, "a citable region is a region");
    }

    /**
     * {@code region} where a reader can be sent to it, and empty where this compile has no source to
     * quote it from.
     *
     * <p>Empty is an answer and not a failure: a clause of a published module is written where this
     * compile cannot show it, and a report about that clause says what it can say without pointing.
     * A region whose ends were read from two different sources is neither — it is a region no walk
     * of one file could produce, and calling it uncitable would file a broken value under the same
     * answer as a published declaration.
     */
    static Optional<CitableRegion> of(Region region) {
        if (region == null || region.start() == null || region.end() == null) {
            return Optional.empty();
        }
        String start = region.start().sourceId();
        String end = region.end().sourceId();
        if (!Objects.equals(start, end)) {
            throw new NotOnePlace(start, end);
        }
        return canShow(region.start()) ? Optional.of(new CitableRegion(region)) : Optional.empty();
    }

    /**
     * Whether this compile can show the reader the place {@code where} names.
     *
     * <p>The question this type is about, on its own, for the callers holding a point rather than a
     * stretch — {@link HelperInliner} deciding whether a body it is copying may keep the positions it
     * was written at. Both read it here: a compile that answered the same question two ways would
     * quote one place and refuse to quote the other, which is how a helper of a module compiled
     * alongside came to be treated as shipped source.
     *
     * <p>A position was read from a source of this compile or it was not, and the sources of a
     * compile are exactly the ones it was handed: the standard library and a module read back off the
     * module path are parsed from text that names no source, which is what says so.
     */
    static boolean canShow(SourcePos where) {
        return where != null && where.sourceId() != null;
    }

    /**
     * A region whose ends were read from two sources.
     *
     * <p>Its own type because the check that would see one swallows what it throws: an analysis that
     * fell over leaves the run-time check standing, which is the right answer for a shape the walk
     * has no rule for and the wrong one here. What this says is that the compiler built a place that
     * is not a place, and a swallowed one comes out as a behavior with nothing to report — the same
     * thing a behavior whose invariants all discharge comes out as. {@link InvariantChecker#gaveUp}
     * refuses it for that reason.
     */
    static final class NotOnePlace extends TheCheckDisagreesWithItself {

        private static final long serialVersionUID = 1L;

        NotOnePlace(String start, String end) {
            super("a region runs from " + start + " to " + end
                    + ", which is not one place in one source");
        }
    }

    /** Where this begins — what a caller comparing two places reads. */
    SourcePos start() {
        return region.start();
    }
}
