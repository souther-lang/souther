package souther.compiler.partition;

import souther.compiler.check.ProjectionEvidence;

import java.util.List;

/**
 * The lines the rules on a position drew through its values, where they drew any.
 *
 * <p>Two cases rather than a list that may be empty, because something else is true only where
 * there are lines. Whether a row can be written at an edge depends on rules this could not read
 * elsewhere in the value the position sits in — a question about the edges, which a position with
 * no edges does not have. Carried beside a possibly-empty list, "uncertain" was a word that meant
 * nothing on its own and was kept true or false by whoever set it.
 */
public sealed interface CutEvidence {

    /** No rule drew a line through this position's values. */
    record None() implements CutEvidence {}

    /**
     * The lines, and how much of the rules the bounds they were drawn from are able to state.
     *
     * <p>The evidence and not a flag read off it. What a reader does with an uncertain edge is the
     * same either way; what it can tell an author is not, and a boolean drops which rule and which
     * position left the range wider than the model. Kept here so that it is not lost one call
     * further on than where it is known.
     *
     * @param cuts       never empty: no lines is {@link None}, which says so
     * @param projection what the bounds of the value this position sits in state of its rules. Where
     *                   it is not exact, a row written at one of these edges may be refused for a
     *                   reason the bounds do not hold. About the edges and about nothing else
     */
    record Present(List<Cut> cuts, ProjectionEvidence projection) implements CutEvidence {

        public Present {
            cuts = List.copyOf(cuts);
            if (cuts.isEmpty()) {
                throw new IllegalArgumentException("no cuts is `None`, which says so");
            }
            if (projection == null) {
                throw new IllegalArgumentException("lines drawn from bounds with no account of them");
            }
        }

        /** Whether a row at one of these edges may turn out to be unwritable. */
        public boolean uncertain() {
            return !projection.isCertified();
        }
    }

    /** The lines as a list, for a reader that only counts them. */
    default List<Cut> cuts() {
        return this instanceof Present present ? present.cuts() : List.of();
    }
}
