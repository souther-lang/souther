package souther.compiler.partition;

import souther.compiler.core.Core;

import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.function.Supplier;

/**
 * A construction a run on the way to a comparison may work out before it
 * ({@link WhatARunWorksOutBeforeACount#constructionsARunMayMeetBefore}), with what it asks as far
 * as that is read and each way a run on the way to the comparison gets to it on.
 *
 * <p>Gathered whatever is read of it, so that what is not read is a reason a stop there is not
 * resolved and never a construction left out.
 *
 * @param made     the construction, the node of the tree that works it out
 * @param asked    what it asks of a run that works it out
 * @param reaches  each way a run on the way to the comparison gets to it, one for each way into
 *                 the body the comparison stands in that it is met before, where the walk met it
 *                 on one way ({@link WhereConstructionsAreMet}): none where no run is shown to get
 *                 to it
 * @param everyWay whether {@code reaches} holds every way a run on the way to the comparison
 *                 gets to it: false where a way into the body the comparison stands in is not
 *                 read, or one it is met on is not one way
 */
record AConstructionOnTheWay(Core.Construct made, Asked asked, List<Reach> reaches,
                             boolean everyWay) {

    AConstructionOnTheWay {
        Objects.requireNonNull(made, "a construction of the tree");
        Objects.requireNonNull(asked, "what it asks, or that it is not read");
        reaches = List.copyOf(reaches);
    }

    /**
     * One way a run on the way to the comparison gets to the construction.
     *
     * @param entry           which way into the body the comparison stands in it is, the same
     *                        number for every construction on it
     * @param toTheComparison what stood on the way to the comparison by that way in
     * @param toIt            what stood on the way to the construction, as the walk met it
     * @param before          what a run on it works out before the construction, where a run
     *                        taking both ways works it out before the comparison unless something
     *                        before it ends the run
     *                        ({@link WhatARunWorksOutBeforeACount#workedOutBeforeAConstruction});
     *                        empty where that is not shown. Worked out the first time it is
     *                        asked: a construction the way to the comparison already holds what
     *                        it asks of is never asked it, and the walk goes down the tree from
     *                        its top
     * @param wayRead         whether {@code toTheComparison} and {@code toIt} hold every
     *                        condition on the way: not where a place inside a function value is
     *                        got to only on some applications, which is said of each application
     *                        and not on the way the walk carries. Worked out the first time it is
     *                        asked, as {@code before} is
     */
    record Reach(int entry, List<OnTheWay> toTheComparison, List<OnTheWay> toIt,
                 Supplier<Optional<WhatARunWorksOutBeforeACount.BeforeAConstruction>> before,
                 Supplier<Boolean> wayRead) {

        Reach {
            toTheComparison = List.copyOf(toTheComparison);
            toIt = List.copyOf(toIt);
            Objects.requireNonNull(before, "what comes before it, or that it is not shown");
            Objects.requireNonNull(wayRead, "whether the way is read whole");
        }
    }

    /** What a construction asks of a run, as far as it is read. */
    sealed interface Asked {

        /** What it asks, read over the names as they stand where it is worked out. */
        record Read(ConstructionAsk ask) implements Asked {}

        /** Nothing: no clause of its type governs what it builds, so it refuses no run. */
        record Nothing() implements Asked {}

        /** What its type asks is not read. */
        record NotRead() implements Asked {}
    }
}
