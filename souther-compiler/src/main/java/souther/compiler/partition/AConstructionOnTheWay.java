package souther.compiler.partition;

import souther.compiler.core.Core;

import java.util.List;
import java.util.Objects;
import java.util.Optional;

/**
 * A construction a run on the way to a comparison may work out before it
 * ({@link WhatARunWorksOutBeforeACount#constructionsARunMayMeetBefore}), with what it asks as far
 * as that is read and the way the walk met it on.
 *
 * <p>Gathered whatever is read of it, so that what is not read is a reason a stop there is not
 * resolved and never a construction left out.
 *
 * @param made  the construction, the node of the tree that works it out
 * @param asked what it asks of a run that works it out
 * @param way   what stood on the way to it, as the walk met it ({@link WhereConstructionsAreMet});
 *              empty where the walk did not meet it on one way
 */
record AConstructionOnTheWay(Core.Construct made, Asked asked, Optional<List<OnTheWay>> way) {

    AConstructionOnTheWay {
        Objects.requireNonNull(made, "a construction of the tree");
        Objects.requireNonNull(asked, "what it asks, or that it is not read");
        Objects.requireNonNull(way, "the way to it, or that it is not one way");
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
