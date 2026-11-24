package souther.compiler.reach;

import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.NumericDomain;

/**
 * What arrives at one comparison, said as much of it as a reader downstream may safely use.
 *
 * <p>Or at one application whose answer states a line — an emptiness check states a size against
 * nought — which is dropped by the same fact a comparison's is. Such an application is answered
 * {@link NothingArrives}, {@link EveryOneStopsInIt} or {@link NoProjection} and never
 * {@link Values}: it has arguments and no
 * side, so there is no position a projection could be of. A reader holding one of these is not
 * holding a comparison's by that alone.
 *
 * <p>A comparison's border stands or falls by whether the values that reach the comparison reach
 * the line it draws — not by whether either of its outcomes is one the paths prove nothing takes.
 * The two questions have different answers: a guard shadowed by a stricter guard above it draws a
 * line nothing arrives at, and a comparison the declarations decide one way is still arrived at by
 * every row there is. This is the fact that separates them, published by the walk that holds it.
 *
 * <p><b>Bottom is its own answer.</b> Whether anything arrives at all is the whole
 * state's answer and never a projection's: a state emptied by its predicates leaves every numeric
 * reading untouched, so bounds read off it say nothing while the state says everything. Read as an
 * interval, an empty arrival came back wide open — which is why {@link NothingArrives} exists as an
 * arm rather than as a shape of {@link Values}, and why nothing may build a {@link Values} from a
 * state that answers empty.
 *
 * <p><b>Getting to it and getting past what it works out are two questions.</b> What arrives is
 * what holds once the comparison's sides are worked out, since a run that stopped working one out
 * is no run the line divides. A run that gets to the comparison and stops in its sides is still a
 * run that got there, and a reader asking whether a run stops in it asks of those. So the two ways
 * of nothing arriving are two arms: {@link NothingArrives}, nothing gets to it, and
 * {@link EveryOneStopsInIt}, every run that gets to it stops in what it works out. A reader asks
 * the question it means ({@link #nothingGetsPast}, {@link #nothingGetsTo}) and never which arm.
 *
 * <p><b>An entry's absence is not a further arm.</b> Whether the walk answered for a comparison is
 * a completeness fact about the analysis, audited where the walk finishes; what one of these means
 * is a restriction a reader may apply. A reader handed nothing degrades to {@link NoProjection},
 * which restricts nothing — the fail-open direction, and the only one an absence may take.
 */
public sealed interface ComparisonArrival {

    /** Whether no run gets past what the comparison works out to a value of it: nothing gets to
     *  it, or every run that does stops there. What a line on it is asked of. */
    default boolean nothingGetsPast() {
        return this instanceof NothingArrives || this instanceof EveryOneStopsInIt;
    }

    /** Whether no run gets to the comparison at all. What whether a run stops in it is asked
     *  of. */
    default boolean nothingGetsTo() {
        return this instanceof NothingArrives;
    }

    /**
     * Nothing arrives at the comparison at all: the conditions on the way there cannot all hold.
     *
     * <p>A proof about the whole abstract state, and with {@link EveryOneStopsInIt} one of the two
     * arms that are one. Everything else here over-approximates; these alone exclude.
     */
    record NothingArrives() implements ComparisonArrival {}

    /**
     * Something gets to the comparison and nothing gets past what it works out: every run there
     * stops in one of its sides. A proof that no value of it is arrived at, as
     * {@link NothingArrives} is, and not that no run gets there.
     */
    record EveryOneStopsInIt() implements ComparisonArrival {}

    /**
     * Not proven empty, and what arrives leaves the value at {@code path} within {@code bounds}.
     *
     * <p>An over-approximation of the values that arrive, and never a claim that any row does:
     * unsettled is not reachable, and a condition the walk could not read narrowed nothing here.
     *
     * <p>A constraint and not an answer about a line. It is taken in beside what the declarations
     * leave and what the way states, and the line is asked of all of them at once: bounds have no
     * word for a value taken out of their middle, so asked on their own they would hold a line at
     * a hole the way leaves.
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
     * proof of anything, so a border under this stands as the declarations and the way leave it.
     */
    record NoProjection() implements ComparisonArrival {}
}
