package souther.compiler.partition;

import java.util.List;
import java.util.Optional;
import java.util.function.Supplier;

/**
 * The ways a run gets to one place the walk met a step a run may stop at, as far as they are
 * read: one for each way a run gets into the tree the step stands in — the behavior's body, a
 * value's template by each build of it, a function value by each call applying it.
 *
 * @param each  each way that is read
 * @param every whether {@code each} is every way a run gets there by
 */
record WaysToASite(List<Reach> each, boolean every) {

    /** No way read. */
    static final WaysToASite NOT_READ = new WaysToASite(List.of(), false);

    WaysToASite {
        each = List.copyOf(each);
    }

    /**
     * One way a run gets to the step.
     *
     * @param way    what stood on the way to it by this way: the way into its tree, and the way
     *               the walk met it on in the tree past what was carried into it
     * @param before what a run by this way works out before the step, in each tree it goes
     *               through and then in the step's own; empty where that is not read
     * @param read   whether the way is on the way the walk carried: outside every function value,
     *               or got to whatever the row is ({@link ClosureApplications}). A way not read
     *               holds what every run by it meets, and not what one run takes
     * @param readUpToTheApplications whether the way is on the way the walk carried as far as
     *               the function value the step stands in, if any: what {@code read} asks, short of
     *               whether the application is made whatever the row is, which a reader judging
     *               each application asks of the application
     */
    record Reach(List<OnTheWay> way,
                 Supplier<Optional<WhatARunWorksOutBeforeACount.BeforeAConstruction>> before,
                 Supplier<Boolean> read, Supplier<Boolean> readUpToTheApplications) {

        Reach {
            way = List.copyOf(way);
        }
    }
}
