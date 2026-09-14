package souther.compiler.reach;

import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.NumericDomain;

/**
 * What arrives at one comparison, said as much of it as a reader downstream may safely use.
 *
 * <p>A comparison's border stands or falls by whether the values that reach the comparison reach
 * the line it draws — not by whether either of its outcomes is one the paths prove nothing takes.
 * The two questions have different answers: a guard shadowed by a stricter guard above it draws a
 * line nothing arrives at, and a comparison the declarations decide one way is still arrived at by
 * every row there is. This is the fact that separates them, published by the walk that holds it.
 *
 * <p><b>Three answers, and bottom is its own.</b> Whether anything arrives at all is the whole
 * state's answer and never a projection's: a state emptied by its predicates leaves every numeric
 * reading untouched, so bounds read off it say nothing while the state says everything. Read as an
 * interval, an empty arrival came back wide open — which is why {@link NothingArrives} exists as an
 * arm rather than as a shape of {@link Values}, and why nothing may build a {@link Values} from a
 * state that answers empty.
 *
 * <p><b>An entry's absence is not a fourth arm.</b> Whether the walk answered for a comparison is a
 * completeness fact about the analysis, audited where the walk finishes; what one of these means is
 * a restriction a reader may apply. A reader handed nothing degrades to {@link NoProjection}, which
 * restricts nothing — the fail-open direction, and the only one an absence may take.
 */
public sealed interface ComparisonArrival {

    /**
     * Nothing arrives at the comparison at all: the conditions on the way there cannot all hold.
     *
     * <p>A proof about the whole abstract state and the one arm that is one. Everything else here
     * over-approximates; this alone excludes.
     */
    record NothingArrives() implements ComparisonArrival {}

    /**
     * Not proven empty, and what arrives leaves the value at {@code path} within {@code bounds}.
     *
     * <p>An over-approximation of the values that arrive, and never a claim that any row does:
     * unsettled is not reachable, and a condition the walk could not read narrowed nothing here. So
     * a line these bounds do not reach is a line no arriving row reaches — that direction is sound —
     * while a line they do reach proves nothing.
     */
    record Values(TermPath path, NumericDomain.Bounds bounds) implements ComparisonArrival {

        public Values {
            if (path == null || bounds == null) {
                throw new IllegalArgumentException(
                        "a projection of what arrives says where and between what");
            }
        }
    }

    /**
     * No arrival projection is provided here, which restricts nothing.
     *
     * <p>One answer with three producers: a comparison that turns on no single position the walk
     * can name a value for, a rule that stands in no body for anything to be on the way to, and a
     * reader handed no entry at all because the walk fell over before finishing. All three read
     * alike because all three license the same thing — nothing. Not being able to project is not a
     * proof of anything, so a border under this stands as the declarations alone leave it.
     */
    record NoProjection() implements ComparisonArrival {}
}
