package souther.compiler.inputs;

import souther.compiler.diag.SourcePos;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
import java.util.Optional;

/**
 * One step of a behavior some run stops at: an operation whose answer is past the ends of its
 * type, or a quotient by nought, or a construction refusing what it is handed.
 *
 * <p>Shown and not a possibility. Said only where a value of the input is shown to exist that
 * takes the way to the step, gets past everything a run works out before it, and stops there:
 * works the operation out past its ends, or does not meet what the construction asks. What the
 * way to it leaves a number holds rows that never get there, and is never what shows one does.
 * Where neither a stop nor that there is none is shown, that is said apart
 * ({@link StepWhereAStopIsNotShown}).
 *
 * <p>Said of the step where it is written, whether or not a comparison comes after it and
 * whatever reads what it works out: a run that stops there stops whatever follows. A run stopped
 * there gets to nothing after it, so what is said of a step is said of no rule after it.
 *
 * <p>And where it is known, at which values every run that gets to the step stops there. Those
 * say where a run stops if one gets there, and name no row: the way to the step is what decides
 * whether a row gets there.
 *
 * @param at            where the step is written
 * @param shown         what shows a run stops in an operation of it, each once; none where it is
 *                      a construction
 * @param constructions what shows a run stops at it, where it is a construction, each once
 * @param everyRunStops the runs of the values at which every run getting to it stops, each once;
 *                      empty where none is known
 * @param keeping       the region of the input that keeps every run getting to the step from
 *                      stopping in it, where it stops where the representation of its number does
 *                      and is over the values of one place ({@link WhatKeepsEveryRunGoing}); none
 *                      where it is any other
 */
public record StepWhereARunMayStop(SourcePos at, List<AStopShown> shown,
                                   List<AConstructionStopShown> constructions,
                                   List<EveryRunStops> everyRunStops,
                                   Optional<WhatKeepsEveryRunGoing> keeping)
        implements WhatIsShownOfAStop {

    public StepWhereARunMayStop {
        Objects.requireNonNull(at, "a run may stop at some step of the model");
        shown = List.copyOf(new LinkedHashSet<>(shown));
        constructions = List.copyOf(new LinkedHashSet<>(constructions));
        if (shown.isEmpty() && constructions.isEmpty()) {
            throw new IllegalArgumentException("a stop said at " + at
                    + " is shown by some value of the input");
        }
        everyRunStops = List.copyOf(new LinkedHashSet<>(everyRunStops));
        Objects.requireNonNull(keeping, "a region kept, or none");
    }

    @Override
    public StepWhereARunMayStop keptBy(Optional<WhatKeepsEveryRunGoing> region) {
        return new StepWhereARunMayStop(at, shown, constructions, everyRunStops, region);
    }

    /** Both readers' findings, as one: the step, with every stop either showed. */
    @Override
    public StepWhereARunMayStop mergedWith(WhatIsShownOfAStop other) {
        if (!(other instanceof StepWhereARunMayStop that) || !at.equals(that.at)) {
            throw new IllegalArgumentException("two findings put together are one step a run may"
                    + " stop at: " + at + " and " + other);
        }
        List<AStopShown> shownBoth = new ArrayList<>(shown);
        shownBoth.addAll(that.shown);
        List<AConstructionStopShown> constructionsBoth = new ArrayList<>(constructions);
        constructionsBoth.addAll(that.constructions);
        List<EveryRunStops> stops = new ArrayList<>(everyRunStops);
        stops.addAll(that.everyRunStops);
        return new StepWhereARunMayStop(at, shownBoth, constructionsBoth, stops,
                WhatKeepsEveryRunGoing.together(keeping, that.keeping));
    }
}
