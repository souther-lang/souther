package souther.compiler.sites;

import souther.compiler.diag.Region;

/**
 * Which occurrence in the authored source a fact is about.
 *
 * <p>The extent and nothing beside it. Within one revision of one source no two authored expressions
 * are written over the same characters, so the stretch an expression covers names it — which
 * ADR-0102 says of the authored tree and of no tree a pass produced. {@link AuthoredSites} checks
 * that it holds of the revision it walks rather than assuming it does.
 *
 * <p>Minted in one place. The constructor is package-private, so an id exists only where that walk
 * made one, and nothing can build one out of a position it was handed: a cursor reaches a site by
 * asking, and reaches none where the source has no expression there. That is why this is not what
 * crosses to a reader either — an editor is answered about what it asked, and has no occurrence of
 * its own to name.
 *
 * <p>Which occurrence, not which elaboration of it. One authored expression inside a helper is
 * checked once per call the helper is expanded into, and a variable a declaration left open is
 * settled per call site ({@code Type.MetaVar}), so the same site stands above as many checked
 * occurrences as there are calls. Nothing here numbers them; what does is the application each
 * elaboration belongs to.
 */
record SourceSiteId(Region extent) {

    SourceSiteId {
        if (extent == null) {
            throw new IllegalArgumentException("an authored site is written somewhere");
        }
    }

    @Override
    public String toString() {
        return extent.start() + ".." + extent.end();
    }
}
