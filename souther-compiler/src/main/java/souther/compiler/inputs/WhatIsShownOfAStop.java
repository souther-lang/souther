package souther.compiler.inputs;

import souther.compiler.check.RuleRef;

import java.util.Optional;

/**
 * What a reading of a rule of the model shows of a run stopping on its way through it: that one
 * does ({@link RuleWhereARunMayStop}), or that whether one does is not resolved
 * ({@link RuleWhereAStopIsNotShown}). One rule may have both said of it, and a rule that has
 * neither said is one no run is shown to stop at, or one nothing read.
 */
public sealed interface WhatIsShownOfAStop permits RuleWhereARunMayStop, RuleWhereAStopIsNotShown {

    /** Which rule. */
    RuleRef rule();

    /** The region of the input that keeps every run getting to the rule from the stops told
     *  ({@link WhatKeepsEveryRunGoing}); none where none is said. */
    Optional<WhatKeepsEveryRunGoing> keeping();

    /** The same, saying {@code region} as the region that keeps the rule's runs going: the one
     *  every reading of the rule says together ({@link RulesWithNoLine.Gathered#found}). */
    WhatIsShownOfAStop keptBy(Optional<WhatKeepsEveryRunGoing> region);

    /** Both readers' findings of one kind about one rule, as one. */
    WhatIsShownOfAStop mergedWith(WhatIsShownOfAStop other);
}
