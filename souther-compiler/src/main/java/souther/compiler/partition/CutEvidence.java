package souther.compiler.partition;

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
     * The lines, and whether a row at one of them may turn out to be unwritable.
     *
     * @param cuts      never empty: no lines is {@link None}, which says so
     * @param uncertain whether some rule reaching the value this position sits in was not read, so
     *                  that a row written at one of these edges may be refused for a reason this
     *                  cannot see. About the edges and about nothing else
     */
    record Present(List<Cut> cuts, boolean uncertain) implements CutEvidence {

        public Present {
            cuts = List.copyOf(cuts);
            if (cuts.isEmpty()) {
                throw new IllegalArgumentException("no cuts is `None`, which says so");
            }
        }
    }

    /** The lines as a list, for a reader that only counts them. */
    default List<Cut> cuts() {
        return this instanceof Present present ? present.cuts() : List.of();
    }
}
