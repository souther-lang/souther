package souther.compiler.partition;

import souther.compiler.inputs.BlockReason;
import souther.compiler.meaning.Proposition;
import souther.compiler.observe.Figure;
import souther.compiler.types.ModelOccurrence;

import java.util.LinkedHashSet;
import java.util.Optional;
import java.util.Set;

/**
 * Where the measuring of one body ends: at the first of some constructs of it that measuring
 * stopped at a figure in.
 *
 * <p><b>What stopped, and nothing reckoned.</b> How many ways there are to choose a case is no
 * number of questions asked: ways no value meets and ways no row takes are never walked, and of a
 * line with more ways than are taken apart none is asked. So what is taken in here is what came of
 * measuring, of the reader that spent the figure: the reading of a condition that says which figure
 * it was read no further at, and the assessment of its lines that says where they decide was not
 * worked out at which. The measuring that hands them over is the one a run that goes on makes, so a
 * run that goes on reports the stop this names.
 *
 * <p><b>Of the constructs it is told, and of no other.</b> They are the ones a change is told of,
 * so that what a reader is told to change is what stopped: a figure met at a construct nothing is
 * told of ends nothing, however dear it is.
 *
 * <p>Nothing is measured past the first, so it is asked as the measuring goes on.
 */
public final class WhatStopsMeasuring {

    private final Set<ModelOccurrence> told;

    private Figure stops;

    private WhatStopsMeasuring(Set<ModelOccurrence> told) {
        this.told = Set.copyOf(told);
    }

    /** At the first of {@code told} that measuring stops at a figure in. */
    public static WhatStopsMeasuring atTheFirstOf(Set<ModelOccurrence> told) {
        return new WhatStopsMeasuring(told);
    }

    /** At none: the measuring is made to its end. */
    public static WhatStopsMeasuring nowhere() {
        return new WhatStopsMeasuring(Set.of());
    }

    /** Whether measuring {@code construct} may end the measuring of the body. */
    boolean isTold(ModelOccurrence construct) {
        return told.contains(construct);
    }

    /** Takes in what {@code construct} was read to state. */
    void reading(ModelOccurrence construct, Proposition stated) {
        if (isTold(construct)) {
            stopped(Proposition.figuresOfReadingsIn(stated));
        }
    }

    /** Takes in what asking where the lines of {@code construct} decide came to. */
    void deciding(ModelOccurrence construct, ComparisonAssessment assessed) {
        if (!isTold(construct)) {
            return;
        }
        Set<Figure> met = new LinkedHashSet<>();
        notWorkedOutAt(assessed, met);
        stopped(met);
    }

    private static void notWorkedOutAt(ComparisonAssessment assessed, Set<Figure> into) {
        switch (assessed) {
            case ComparisonAssessment.Several several -> several.parts().forEach(part ->
                    notWorkedOutAt(part.line(), into));
            case ComparisonAssessment.Unread unread -> unread.places().stops().forEach(stop -> {
                if (stop.reason()
                        instanceof BlockReason.WhereALineDecidesNotWorkedOut(var figures)) {
                    into.addAll(figures);
                }
            });
            default -> { }
        }
    }

    private void stopped(Set<Figure> met) {
        if (stops == null && !met.isEmpty()) {
            stops = Figure.inOrder(met).getFirst();
        }
    }

    /** Whether the measuring ended. */
    public boolean isShown() {
        return stops != null;
    }

    /** The figure the measuring ended at; empty where it goes on. */
    public Optional<Figure> figure() {
        return Optional.ofNullable(stops);
    }
}
