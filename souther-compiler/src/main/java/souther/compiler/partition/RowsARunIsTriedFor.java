package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

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
 * said ({@link #repertoireOf}), and never proves it empty.
 */
public final class RowsARunIsTriedFor {

    /** The values a whole number is written at, in the order they are tried. */
    private static final List<Long> VALUES = List.of(0L, 1L, -1L, 2L);

    /**
     * The most elements a container is written holding: the edge of the population the
     * candidates are, which {@link #sizes} says, and not a
     * figure a search stops at — every candidate inside it is tried.
     */
    private static final int MOST_ELEMENTS = 6;

    private RowsARunIsTriedFor() {}

    /**
     * Which population the candidates for {@code goal} are: the one repertoire that says what
     * {@link #candidates} varies, so that what is reported is what was written. A goal that names
     * containers is tried at sizes, one that names whole numbers outside a container at values,
     * and each axis a goal does not name is not varied.
     */
    static CompositionRepertoire repertoireOf(PointSearchGoal.ByObservation goal) {
        boolean sizes = !goal.lengths().isEmpty();
        boolean values = !goal.values().isEmpty();
        if (sizes && values) {
            return CompositionRepertoire.ROWS_A_RUN_IS_TRIED_FOR_AT_SIZES_AND_VALUES;
        }
        if (sizes) {
            return CompositionRepertoire.ROWS_A_RUN_IS_TRIED_FOR_AT_SIZES;
        }
        return values ? CompositionRepertoire.ROWS_A_RUN_IS_TRIED_FOR_AT_VALUES
                : CompositionRepertoire.ROWS_A_RUN_IS_TRIED_FOR_AT_NO_PLACE;
    }

    /**
     * What is said of the containers a candidate is written for. How an element is written is the
     * type's own ({@code Witnesses}), so it is not said here. The figures of this and {@link
     * #values} sit in no comma of their own, so a population stays one item in the
     * comma-separated list of populations it is read among.
     */
    public static String sizes() {
        return "the containers the comparison names each holding the same number of elements from"
                + " 0 to " + MOST_ELEMENTS + " built as their types hold that many";
    }

    /** What is said of the whole numbers outside a container a candidate is written for. */
    public static String values() {
        return "the whole numbers it names outside a container all at one of {"
                + VALUES.stream().map(String::valueOf).collect(Collectors.joining(", ")) + "}";
    }

    /**
     * The population the report says this compiler writes some of: the rows a run comes to the
     * item at, which the candidates are some of. Said as the candidates in a parenthesis and not
     * as what is left out, since it is read after "writes some of" and an "other than" there reads
     * as the rows this compiler does write.
     */
    public static String population(String candidates) {
        return "the rows whose run works out a number at the item (written with " + candidates
                + ")";
    }

    /** Every candidate for {@code goal}, in the order they are tried, none of them empty. */
    static List<Map<RealizationTarget, Place>> candidates(PointSearchGoal.ByObservation goal) {
        if (goal.lengths().isEmpty() && goal.values().isEmpty()) {
            return List.of();
        }
        int most = goal.lengths().isEmpty() ? 0 : MOST_ELEMENTS;
        List<Long> values = goal.values().isEmpty() ? List.of(0L) : VALUES;
        List<Map<RealizationTarget, Place>> out = new ArrayList<>();
        for (int size = 0; size <= most; size++) {
            for (long value : values) {
                Map<RealizationTarget, Place> fixing = new LinkedHashMap<>();
                for (NumericTerm.FromOnePosition length : goal.lengths()) {
                    fixing.put(RealizationTarget.of(length), Count.of(size));
                }
                for (NumericTerm.FromOnePosition number : goal.values()) {
                    fixing.put(RealizationTarget.of(number), Count.of(value));
                }
                out.add(fixing);
            }
        }
        return out;
    }
}
