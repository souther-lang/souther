package souther.compiler.partition;

import souther.compiler.observe.Figure;

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.List;
import java.util.Set;

/**
 * What a search that stopped found out and was stopped by, kept whole so that two of them are one.
 *
 * <p>A search looked for again, or along several ways, is several searches whose answer is one.
 * What each found out is still true of the combination after the next one came back, so the answer
 * is what all of them came to and never the last: a figure one of them met is a number somebody can
 * raise whichever came after it.
 *
 * @param found                  what the searches found out, added up
 * @param boundsReached          the bounds of this search's own any of them stopped at
 * @param metARunNothingWatched  whether any of them ran a candidate and nothing could say what it
 *                               did
 * @param planCut                the figures that cut short the plan any of them ran over
 */
record Stopped(SearchShortfall found, List<Figure> boundsReached, boolean metARunNothingWatched,
               Set<CompositionBudget> planCut) {

    Stopped {
        boundsReached = Figure.inOrder(boundsReached);
        planCut = InDeclaredOrder.of(planCut);
    }

    /** What two searches stopped by, together. */
    Stopped and(Stopped other) {
        List<Figure> bounds = new ArrayList<>(boundsReached);
        bounds.addAll(other.boundsReached());
        Set<CompositionBudget> cut = EnumSet.noneOf(CompositionBudget.class);
        cut.addAll(planCut);
        cut.addAll(other.planCut());
        return new Stopped(found.and(other.found()), bounds,
                metARunNothingWatched || other.metARunNothingWatched(), cut);
    }
}
