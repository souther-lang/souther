package souther.compiler.partition;

import souther.compiler.coverage.CoverageSites;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;


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
public record GuardEdge(CoverageSites.GuardRef guard, int site, NumericTerm term,
                        Place low, boolean lowInclusive,
                        Place high, boolean highInclusive) {

    /** The values above {@code value}, including it where {@code inclusive}. */
    public static GuardEdge above(CoverageSites.GuardRef guard, int site, NumericTerm term,
                                  Place value, boolean inclusive) {
        return new GuardEdge(guard, site, term, value, inclusive, null, false);
    }

    /** The values below {@code value}, including it where {@code inclusive}. */
    public static GuardEdge below(CoverageSites.GuardRef guard, int site, NumericTerm term,
                                  Place value, boolean inclusive) {
        return new GuardEdge(guard, site, term, null, false, value, inclusive);
    }

    public String behavior() {
        return guard.behavior();
    }

    /** Where the value this edge is about sits. Not what it is about: that is {@link #term()}. */
    public TermPath path() {
        return term.path();
    }

    /** An end of this edge, or no end at all where the edge is open in that direction. */
    private static Endpoint end(Place at, boolean inclusive) {
        return at == null ? null : new Endpoint(at, inclusive);
    }
}
