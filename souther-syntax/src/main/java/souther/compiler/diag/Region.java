package souther.compiler.diag;


/**
 * A source range from {@code start} (inclusive) to {@code end} (exclusive), each a
 * {@link SourcePos}. A single token is {@code start} plus its text length; when only a point is
 * known, {@code start == end}.
 *
 * <p>Everything here is measured in UTF-16 code units, because that is what a {@link SourcePos}
 * column is — an index into the line, which is what the LSP exchanges and what a JSON diagnostic
 * publishes. It is not a count of screen columns and not a number of characters to draw. A
 * full-width character is one unit and two columns, so a caller that handed a screen width to
 * {@link #ofWidth} would move the end of a published range by the wrong amount. Turning any of this
 * into a place on the screen is {@code HumanRenderer}'s, and it needs the source line to do it.
 */
public record Region(SourcePos start, SourcePos end) {

    /** A zero-width region at a single point. */
    public static Region point(SourcePos p) {
        return new Region(p, p);
    }

    /** A region beginning at {@code start} and running {@code width} UTF-16 code units along the
     * same line — the length of the text it covers, not the room that text takes on a screen. The
     * end is in the file the start is in: a region does not leave the source it began in. */
    public static Region ofWidth(SourcePos start, int width) {
        int w = Math.max(0, width);
        return new Region(start,
                new SourcePos(start.line(), start.column() + w, start.sourceId()));
    }

    /**
     * Whether {@code inner} lies within {@code outer}, ends allowed to meet — and vacuously so where
     * either of them is nowhere, there being no two places to disagree about.
     *
     * <p>What a caller holding a form and something written inside it checks: an expression and the
     * name it consists of, a construction and the field it sets. Regions in two files are not one
     * inside the other however their numbers compare.
     */
    public static boolean encloses(Region outer, Region inner) {
        if (outer == null || inner == null) {
            return true;
        }
        if (!java.util.Objects.equals(outer.start.sourceId(), inner.start.sourceId())) {
            return false;
        }
        return !before(inner.start, outer.start) && !before(outer.end, inner.end);
    }

    /** Whether {@code a} comes before {@code b} in the file they share. */
    private static boolean before(SourcePos a, SourcePos b) {
        return a.line() != b.line() ? a.line() < b.line() : a.column() < b.column();
    }

    /**
     * How much of the start line the region covers, in UTF-16 code units, and at least one.
     *
     * <p>A region that ends on a later line answers one. How much of the first line such a region
     * covers is not written down anywhere here, and no reader has needed it: the one caller cuts
     * this many units out of the line and measures what it cut.
     */
    public int sourceSpan() {
        if (end.line() != start.line()) {
            return 1;
        }
        return Math.max(1, end.column() - start.column());
    }
}
