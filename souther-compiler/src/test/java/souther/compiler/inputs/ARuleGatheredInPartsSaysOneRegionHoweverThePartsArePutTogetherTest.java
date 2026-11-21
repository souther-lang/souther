package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleCitation;
import souther.compiler.check.RuleRef;
import souther.compiler.check.RuleReportAnchor;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.ModelOccurrences;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

import java.math.BigInteger;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The findings of one rule gathered in parts and the parts put together say one region, however
 * the parts are grouped: what shows a value holding all of it at once is kept until a report says
 * it, and a part that alone shows none says nothing of what another part shows.
 */
class ARuleGatheredInPartsSaysOneRegionHoweverThePartsArePutTogetherTest {

    private static final RuleCitation RULE = new RuleCitation.Written(
            new RuleRef.Comparison("b", new SourceConstructOrigin(
                    new WrittenOwner.Body("m", "b"), 1, 1, SourceConstruct.IF)),
            new RuleReportAnchor.ByTheReadingThatMetIt("Main", "b", 0));

    private static final ABoundThatKeepsEveryRunGoing X = on("x");
    private static final ABoundThatKeepsEveryRunGoing Y = on("y");

    private static ABoundThatKeepsEveryRunGoing on(String parameter) {
        return new ABoundThatKeepsEveryRunGoing(
                new ABoundThatKeepsEveryRunGoing.Holder.AParameter(parameter, "Int"), true,
                BigInteger.TEN, new ObservedValue.Integer(10),
                new ABoundThatKeepsEveryRunGoing.Held(null, null));
    }

    /** A part holding one finding of the rule, which keeps the region {@code bounds} declare. */
    private static RulesWithNoLine part(ABoundThatKeepsEveryRunGoing... bounds) {
        RulesWithNoLine.Gathered gathered = new RulesWithNoLine.Gathered();
        gathered.mayStopARun(RULE, ModelOccurrences.NONE,
                List.of(new AStopShown("x + 1", List.of())), List.of(), List.of(),
                WhatKeepsEveryRunGoing.of(List.of(bounds)));
        return gathered.found();
    }

    /** What a report says the rule keeps, once the parts are put together. */
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
