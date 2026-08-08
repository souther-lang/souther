package souther.compiler.partition;

import souther.compiler.coverage.CoverageSites;
import souther.compiler.numeric.NumericDomain;

import java.math.BigDecimal;

/**
 * One side of a guard, and the values of one position that take it.
 *
 * <p>Not a {@link Threshold}. A threshold says which side of a line the line's own value belongs to,
 * which is what decides where one class ends and the next begins. This says which values reach one
 * arm, which is what decides whether that arm is an arm at all. The two are not the same question and
 * neither is derivable from the other: {@code x <= c} and {@code x > c} both put {@code c} on the low
 * side, and their {@code then} arms are opposite halves of the line.
 *
 * <p>An absent end is unbounded there. The openness here is exact — it is read off the comparison the
 * body is written with — and is not the openness a derived bound loses (#483): nothing about it comes
 * through {@link NumericDomain}.
 *
 * @param guard the {@code if} this is one arm of, which is also what says which behavior it is in
 * @param site  the probe number of that arm, the same identity a branch obligation is counted by
 */
public record GuardEdge(CoverageSites.GuardRef guard, int site, TermPath path,
                        BigDecimal low, boolean lowInclusive,
                        BigDecimal high, boolean highInclusive) {

    /** The values above {@code value}, including it where {@code inclusive}. */
    public static GuardEdge above(CoverageSites.GuardRef guard, int site, TermPath path,
                                  BigDecimal value, boolean inclusive) {
        return new GuardEdge(guard, site, path, value, inclusive, null, false);
    }

    /** The values below {@code value}, including it where {@code inclusive}. */
    public static GuardEdge below(CoverageSites.GuardRef guard, int site, TermPath path,
                                  BigDecimal value, boolean inclusive) {
        return new GuardEdge(guard, site, path, null, false, value, inclusive);
    }

    public String behavior() {
        return guard.behavior();
    }

    /**
     * Whether nothing this edge admits is a value the position can hold.
     *
     * <p>The one place the two are compared, so that what changes when a bound learns its own openness
     * changes here and nowhere else.
     *
     * <p>Sound while {@code admissible} is as wide as or wider than the values that can really be
     * written: an edge disjoint from a superset is disjoint from the set. The other direction is not
     * claimed — an edge that meets these bounds is not thereby reachable, because a rule they could
     * not hold can still refuse every value in the overlap. So only this answer excludes anything,
     * and being unable to prove disjointness costs a report nothing but an obligation nobody can
     * meet.
     */
    public boolean provenDisjoint(NumericDomain.Bounds admissible) {
        if (admissible == null) {
            return false;
        }
        if (low != null && admissible.max() != null) {
            int order = low.compareTo(admissible.max());
            if (order > 0 || (order == 0 && !lowInclusive)) {
                return true;
            }
        }
        if (high != null && admissible.min() != null) {
            int order = high.compareTo(admissible.min());
            if (order < 0 || (order == 0 && !highInclusive)) {
                return true;
            }
        }
        return false;
    }
}
