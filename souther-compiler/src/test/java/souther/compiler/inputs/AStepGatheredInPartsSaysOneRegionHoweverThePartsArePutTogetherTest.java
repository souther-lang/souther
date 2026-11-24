package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourcePos;
import souther.compiler.observe.ObservedValue;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The findings of one step gathered in parts and the parts put together say one region, however
 * the parts are grouped: what shows a value holding all of it at once is kept until a report says
 * it, and a part that alone shows none says nothing of what another part shows.
 */
class AStepGatheredInPartsSaysOneRegionHoweverThePartsArePutTogetherTest {

    private static final SourcePos STEP = new SourcePos(1, 1);

    private static final ABoundThatKeepsEveryRunGoing X = on("x");
    private static final ABoundThatKeepsEveryRunGoing Y = on("y");

    private static ABoundThatKeepsEveryRunGoing on(String parameter) {
        return new ABoundThatKeepsEveryRunGoing(
                new ABoundThatKeepsEveryRunGoing.Holder.AParameter(parameter, "Int"), true,
                BigInteger.TEN, new ObservedValue.Integer(10));
    }

    /** A part holding one finding of the step, which keeps the region {@code bounds} declare. */
    private static RulesWithNoLine part(ABoundThatKeepsEveryRunGoing... bounds) {
        Map<ABoundThatKeepsEveryRunGoing.Holder, ABoundThatKeepsEveryRunGoing.Held> held =
                new LinkedHashMap<>();
        for (ABoundThatKeepsEveryRunGoing each : bounds) {
            held.put(each.holder(), new ABoundThatKeepsEveryRunGoing.Held(null, null));
        }
        RulesWithNoLine.Gathered gathered = new RulesWithNoLine.Gathered();
        gathered.stopped(new StepWhereARunMayStop(STEP,
                List.of(new AStopShown("x + 1", List.of())), List.of(), List.of(),
                WhatKeepsEveryRunGoing.of(List.of(bounds), held)));
        return gathered.found();
    }

    /** What a report says the step keeps, once the parts are put together. */
    private static Optional<Set<ABoundThatKeepsEveryRunGoing>> said(RulesWithNoLine parts) {
        return parts.stopping().getFirst().keeping().flatMap(WhatKeepsEveryRunGoing::said)
                .map(WhatKeepsEveryRunGoing::bounds);
    }

    @Test
    void thePartsGroupedEitherWaySayOneRegion() {
        RulesWithNoLine ofX = part(X);
        RulesWithNoLine ofY = part(Y);
        RulesWithNoLine ofBoth = part(X, Y);

        assertEquals(Optional.of(Set.of(X, Y)), said(ofX.and(ofY).and(ofBoth)));
        assertEquals(Optional.of(Set.of(X, Y)), said(ofX.and(ofY.and(ofBoth))));
        assertEquals(Optional.empty(), said(ofX.and(ofY)));
    }
}
