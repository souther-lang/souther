package souther.compiler.diag;

/**
 * Refuses a region that is not one place before anything is asked of it.
 *
 * <p>The whole of where a position is, and not just the file. A region whose ends are in two places
 * is a place that is two places, and a placement is what says which place one end is in — so this is
 * one comparison rather than a file test and a provenance test that could be kept in step by hand.
 * Read off the start alone, the second end's answer would go unrecorded: a region running from a
 * copy of {@code A} to a copy of {@code B} would come back as a report about {@code A}, and nothing
 * anywhere would say otherwise.
 *
 * <p>Here rather than on {@link Region}, which is a pair of positions and is built by every pass;
 * this is where a pair is asked to be a place. Measured before it was written: no region in the
 * compiler's own corpus has ends that disagree about provenance.
 *
 * <p>Its own class because more than one type asks it. {@link DiagnosticPlace} asks it of a region a
 * reader may be sent to and {@link UnnamedRegion} of one nobody can be sent to, and those are the
 * same question about the pair — a region that is two places is two places whichever of them it is
 * in. Written twice they would be one question with two answers, which is the shape this package
 * exists to close.
 */
final class OnePlace {

    private OnePlace() {
    }

    static void heldTo(Region region) {
        if (region == null) {
            throw new DiagnosticPlace.NotAPlace("a label is about a region and was given none");
        }
        SourcePos start = region.start();
        SourcePos end = region.end();
        if (start == null || end == null) {
            throw new DiagnosticPlace.NotAPlace("a region a label is about has two ends: " + region);
        }
        if (!start.placement().equals(end.placement())) {
            throw new DiagnosticPlace.NotOnePlace("a region runs from " + start.placement() + " to "
                    + end.placement() + ", which is not one place");
        }
    }
}
