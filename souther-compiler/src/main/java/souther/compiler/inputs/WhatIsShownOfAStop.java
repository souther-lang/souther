package souther.compiler.inputs;

import souther.compiler.diag.SourcePos;

import java.util.Optional;

/**
 * What the judgement of a step of a behavior shows of a run stopping there: that one does
 * ({@link StepWhereARunMayStop}), or that whether one does is not resolved
 * ({@link StepWhereAStopIsNotShown}). One step may have both said of it, and a step that has
 * neither said is one no run is shown to stop at.
 */
public sealed interface WhatIsShownOfAStop
        permits StepWhereARunMayStop, StepWhereAStopIsNotShown {

    /** Where the step is written. */
    SourcePos at();

    /** The region of the input that keeps every run getting to the step from the stops told
     *  ({@link WhatKeepsEveryRunGoing}); none where none is said. */
    Optional<WhatKeepsEveryRunGoing> keeping();

    /** The same, saying {@code region} as the region that keeps the step's runs going: the one
     *  every reading of the step says together ({@link RulesWithNoLine.Gathered#found}). */
    WhatIsShownOfAStop keptBy(Optional<WhatKeepsEveryRunGoing> region);

    /** Both readers' findings of one kind about one step, as one. */
    WhatIsShownOfAStop mergedWith(WhatIsShownOfAStop other);
}
