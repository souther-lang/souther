package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

/**
 * One assignment of some positions that a region admits, or nothing.
 *
 * <p><b>A witness and not a representative.</b> What a region leaves a position is a run, and every
 * value of it is as good as any other until the next position is asked — at which point most of
 * them may leave nothing. Asked one position at a time and answered with the first value each run
 * offers, a set of conditions that has an assignment comes back as one that has none: the first
 * choice was not wrong about its own position and was wrong about the pair.
 *
 * <p>So what this is asked for is the assignment, and the values it tries are its own business. A
 * caller holding conditions it wants a row written under puts them to the region and is told whether
 * there is one, which is a question about the region rather than about the order values happen to
 * be offered in.
 *
 * <p><b>Not a proof of the opposite.</b> Coming back with nothing says these values were tried and
 * none of them was an assignment. A region that leaves a position a run without an end is sampled
 * rather than walked, so what is here is bounded and a longer search may find one — which is the
 * same thing {@link SearchRegion#emptiness()} promises of itself: not being empty is not a value
 * existing, and this is where a caller finds out which.
 *
 * <p>Apart from {@link LevelRealizer} on purpose. That one is asked where a row has to stand for it
 * to be at a coverage item, which is a question about a border; this is asked whether a set of
 * conditions has an assignment at all, which is a question about a region and has no item in it.
 * Answered together, the realizer would be deciding what a row is as well as where its item is.
 */
final class NumericWitness {

    /**
     * How many values of one position are tried before this gives up on it.
     *
     * <p>Small, and bounded for the reason every other walk here is: a run without an end is
     * sampled. What stepping past a value buys is the next position having something left, and a
     * condition relating two positions gives that up within a step or two of the end it is written
     * against — past which the values being tried are ones the same condition already refused.
     */
    private static final int VALUES_A_POSITION_IS_TRIED_AT = 8;

    /**
     * Where each of {@code terms} may stand together inside {@code within}, or null where this found
     * no such assignment.
     *
     * @param on what each position is counted on, or null for one this has no order for — which is
     *           a position no value is chosen at here, and the whole assignment is refused rather
     *           than made without it
     */
    static Map<NumericTerm.FromOnePosition, Place> of(
            SearchRegion within, List<NumericTerm.FromOnePosition> terms,
            Function<NumericTerm, Carrier> on) {
        Map<NumericTerm.FromOnePosition, Place> standing = new LinkedHashMap<>();
        return walk(within, terms, 0, on, standing) ? standing : null;
    }

    /**
     * The walk from one position on, with the ones before it fixed in {@code within}.
     *
     * <p>Depth-first, and the region is narrowed as each is chosen rather than at the end: a value
     * that leaves the rest nothing is stepped past here, where there is still another to try, and
     * not reported once every position has been given one.
     */
    private static boolean walk(SearchRegion within, List<NumericTerm.FromOnePosition> terms,
                                int at,
                                Function<NumericTerm, Carrier> on,
                                Map<NumericTerm.FromOnePosition, Place> standing) {
        if (at == terms.size()) {
            return true;
        }
        NumericTerm.FromOnePosition term = terms.get(at);
        Carrier carrier = on.apply(term);
        NumericDomain.Bounds runs = within.runsBetween(term);
        if (carrier == null || runs == null) {
            return false;
        }
        Place first = carrier.onTheGrid(carrier.somethingInside(runs.min(), runs.max()));
        if (first == null) {
            return false;
        }
        for (Place tried : Outwards.from(first, Count.of(1), carrier, runs,
                VALUES_A_POSITION_IS_TRIED_AT)) {
            if (!(tried instanceof Count count)) {
                continue;
            }
            SearchRegion next = within.given(term, count);
            if (next.emptiness().isPresent()) {
                continue;
            }
            standing.put(term, tried);
            if (walk(next, terms, at + 1, on, standing)) {
                return true;
            }
            standing.remove(term);
        }
        return false;
    }

    private NumericWitness() {}
}
