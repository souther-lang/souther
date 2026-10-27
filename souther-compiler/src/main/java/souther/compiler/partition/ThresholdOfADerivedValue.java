package souther.compiler.partition;

import souther.compiler.numeric.ExactRatio;

import java.util.Objects;

/**
 * One threshold of a computation cut at several places, which is what an ON and an OFF point are
 * owed for once for each of.
 *
 * <p>Both are a threshold of one computation, and two computations never share one. Cut at the
 * same places, the calls of a helper are one computation ({@link DerivedValues}); cut at different
 * places they are two, and a row on a border of one is on no border of the other. A number the
 * bounds of two computations come to is no reason to join them: the fault is a bound written wrong,
 * and a row exercises the bounds of the computation it runs through.
 *
 * <p>A bound of the table the comparison was written against is one threshold however many places
 * its computation is cut at ({@link WrittenAt}): a row at its points shows where the bound falls,
 * because every place is the same bound written once. Three months weighed into their average cut
 * the total of the three at three times the bound, and that total is the place's and not the
 * table's.
 *
 * <p>Where no bound is written ({@link CutAt}) the threshold is the place the computation is cut
 * at. Two readings that cannot be told to compare against one bound are two thresholds: owing more
 * than there is leaves a point asking for a row, while joining what is not one would report a
 * point as answered that no row stands at.
 */
public sealed interface ThresholdOfADerivedValue {

    /**
     * The bound the comparison was written against, as the table holds it.
     *
     * @param value the computation the bound is a threshold of
     * @param level the number one side of the comparison is on every run
     */
    record WrittenAt(DerivedValue value, ExactRatio level) implements ThresholdOfADerivedValue {

        public WrittenAt {
            Objects.requireNonNull(value, "a threshold is a threshold of some computation");
            Objects.requireNonNull(level, "a bound is a number");
        }
    }

    /**
     * The place a computation is cut at.
     *
     * <p>The computation and the place, and never the place alone: one comparison read at two
     * calls cut at different places is two computations, and a row on a border of one is on no
     * border of the other.
     */
    record CutAt(DerivedValue value, DerivedValue.Place place)
            implements ThresholdOfADerivedValue {

        public CutAt {
            Objects.requireNonNull(value, "a threshold is a threshold of some computation");
            Objects.requireNonNull(place, "a computation is cut at some place");
        }
    }
}
