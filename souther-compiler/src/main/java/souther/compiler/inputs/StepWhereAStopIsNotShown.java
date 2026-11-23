package souther.compiler.inputs;

import souther.compiler.diag.SourcePos;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
import java.util.Optional;

/**
 * One step of a behavior where whether a run stops there is not resolved: neither that one does
 * nor that none does is shown.
 *
 * <p>Not a stop, and not that there is none. Said of the step where it is written, beside a stop
 * shown at the same step ({@link StepWhereARunMayStop}): showing that one operation of it stops a
 * run says nothing of another.
 *
 * <p>Of an operation ({@code notShown}, which and why for each), or of a construction
 * ({@code asks}, what it asks where that is read and why).
 *
 * @param at            where the step is written
 * @param notShown      each operation of it neither is shown of, and why, each once
 * @param asks          where it is a construction, what it asks where that is read and why
 * @param everyRunStops the values at which every run getting to the step stops, each once, where
 *                      that is known: a proof of where a run stops if one gets there, and not that
 *                      one does, which is what is not resolved here
 * @param keeping       the region of the input that keeps every run getting to the step from the
 *                      stops told ({@link WhatKeepsEveryRunGoing}); none where it is not said
 */
public record StepWhereAStopIsNotShown(SourcePos at, List<AStopNotShown> notShown,
                                       List<AConstructionStopNotShown> asks,
                                       List<EveryRunStops> everyRunStops,
                                       Optional<WhatKeepsEveryRunGoing> keeping)
        implements WhatIsShownOfAStop {

    public StepWhereAStopIsNotShown {
        Objects.requireNonNull(at, "a stop is not shown at some step of the model");
        notShown = List.copyOf(new LinkedHashSet<>(notShown));
        asks = List.copyOf(new LinkedHashSet<>(asks));
        everyRunStops = List.copyOf(new LinkedHashSet<>(everyRunStops));
        Objects.requireNonNull(keeping, "a region kept, or none");
        if (notShown.isEmpty() && asks.isEmpty()) {
            throw new IllegalArgumentException("a stop is not shown for some reason: " + at);
        }
    }

    @Override
    public StepWhereAStopIsNotShown keptBy(Optional<WhatKeepsEveryRunGoing> region) {
        return new StepWhereAStopIsNotShown(at, notShown, asks, everyRunStops, region);
    }

    /** Both readers' findings, as one: the step, with every operation either left unresolved,
     *  every construction either told of and every stop either proved. */
    @Override
    public StepWhereAStopIsNotShown mergedWith(WhatIsShownOfAStop other) {
        if (!(other instanceof StepWhereAStopIsNotShown that) || !at.equals(that.at)) {
            throw new IllegalArgumentException("two findings put together are one step whose "
                    + "stop is not shown: " + at + " and " + other);
        }
        List<AStopNotShown> open = new ArrayList<>(notShown);
        open.addAll(that.notShown);
        List<AConstructionStopNotShown> asked = new ArrayList<>(asks);
        asked.addAll(that.asks);
        List<EveryRunStops> stops = new ArrayList<>(everyRunStops);
        stops.addAll(that.everyRunStops);
        return new StepWhereAStopIsNotShown(at, open, asked, stops,
                WhatKeepsEveryRunGoing.together(keeping, that.keeping));
    }
}
