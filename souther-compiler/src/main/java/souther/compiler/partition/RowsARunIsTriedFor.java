package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The rows a number only a run works out is looked for with, in the order they are tried.
 *
 * <p>Candidates and nothing more. Nothing says where the input has to stand for the run to come
 * to the item ({@link PointSearchGoal.ByObservation}), so a row is written at a few sizes and
 * values of the places the comparison names, and the search that asks for one runs it and reads
 * what the run worked out — the same building, running and reading every point a search finds a
 * value for goes through. Which is why each is a place for each number, as a solver's answer is,
 * and is offered the way every placement is ({@link LevelRealizer#realize(PointSearchGoal,
 * SearchRegion, WitnessSearch, ValuesTried)}).
 *
 * <p>A candidate is every container among those places holding one number of elements, which are
 * written the way a row's values are written where nothing asks anything of them, and every
 * whole number among those places outside a container at one value. The population is every
 * size crossed with every value, and every one of them is tried ({@link
 * PointSearchGoal#askedAtMost}): it is small, and cut at a figure the order would decide which
 * sizes and values are ever reached. The order decides only how soon: each size is tried with
 * every value before the next size is, so a size is reached at every value at once and the sizes
 * a count is made of come early.
 *
 * <p>What none of them found is not that nothing is there: a row a run comes to the item at only
 * with elements of other values, elements unlike one another, or a size or value past these, is
 * found by none of them. So running out of candidates leaves the item owed, with the population
 * said ({@link CompositionRepertoire#ROWS_A_RUN_IS_TRIED_FOR}), and never proves it empty.
 */
final class RowsARunIsTriedFor {

    /** The values a whole number is written at, in the order they are tried. */
    private static final List<Long> VALUES = List.of(0L, 1L, -1L, 2L);

    /**
     * The most elements a container is written holding: the edge of the population the
     * candidates are, which {@link CompositionRepertoire#ROWS_A_RUN_IS_TRIED_FOR} says, and not a
     * figure a search stops at — every candidate inside it is tried.
     */
    private static final int MOST_ELEMENTS = 6;

    private RowsARunIsTriedFor() {}

    /** Every candidate for {@code goal}, in the order they are tried, none of them empty. */
    static List<Map<RealizationTarget, Place>> candidates(PointSearchGoal.ByObservation goal) {
        List<Map<RealizationTarget, Place>> out = new ArrayList<>();
        if (goal.lengths().isEmpty() && goal.values().isEmpty()) {
            return out;
        }
        int most = goal.lengths().isEmpty() ? 0 : MOST_ELEMENTS;
        for (int size = 0; size <= most; size++) {
            for (long value : VALUES) {
                Map<RealizationTarget, Place> fixing = new LinkedHashMap<>();
                for (NumericTerm.FromOnePosition length : goal.lengths()) {
                    fixing.put(RealizationTarget.of(length), Count.of(size));
                }
                for (NumericTerm.FromOnePosition number : goal.values()) {
                    fixing.put(RealizationTarget.of(number), Count.of(value));
                }
                if (!out.contains(fixing)) {
                    out.add(fixing);
                }
            }
        }
        return out;
    }
}
