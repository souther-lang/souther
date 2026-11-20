package souther.compiler.inputs;

import souther.compiler.check.RuleRef;

import java.util.List;

/**
 * What a reading of a rule of the model shows of a run stopping on its way through it: that one
 * does ({@link RuleWhereARunMayStop}), or that whether one does is not resolved
 * ({@link RuleWhereAStopIsNotShown}). One rule may have both said of it, and a rule that has
 * neither said is one no run is shown to stop at, or one nothing read.
 */
public sealed interface WhatIsShownOfAStop permits RuleWhereARunMayStop, RuleWhereAStopIsNotShown {

    /** Which rule. */
    RuleRef rule();

    /** The bounds on the input that keep every run getting to the rule from the stops told,
     *  each said as far out as it can be where a run just past it is shown to stop
     *  ({@link ABoundThatKeepsEveryRunGoing#furthestOut}). */
    List<ABoundThatKeepsEveryRunGoing> keeping();

    /** Both readers' findings of one kind about one rule, as one. */
    WhatIsShownOfAStop mergedWith(WhatIsShownOfAStop other);
}
