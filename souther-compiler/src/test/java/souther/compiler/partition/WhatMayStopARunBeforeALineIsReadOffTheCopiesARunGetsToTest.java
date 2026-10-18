package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.coverage.EmittedComparisonState;
import souther.compiler.coverage.Numberings;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.reach.ComparisonArrival;
import souther.compiler.reach.WhatMayStopARun;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What may stop a run on the way to a line is read off the places the rule is watched at that a
 * run gets to.
 *
 * <p>One rule may stand in the tree that runs more than once — a library operation applying a
 * closure it was handed in two places writes it twice — and the line is drawn once over every copy.
 * A copy a run gets to with everything on the way read is a way to the rule that is all read, and
 * then the line is. A copy nothing gets to is no way to the rule at all: that nothing on the way to
 * it may stop a run is because nothing is on the way to it, which shows nothing of the copies a run
 * does get to.
 */
class WhatMayStopARunBeforeALineIsReadOffTheCopiesARunGetsToTest {

    private static final List<WhatMayStopARun> PAST_A_PRODUCT =
            List.of(new WhatMayStopARun.AnOperator());

    private static EmittedComparisonState.Observation arrivingPast(List<WhatMayStopARun> stops) {
        return copy(new ComparisonArrival.Values(TermPath.of("b"),
                new NumericDomain.Bounds(null, null)), stops);
    }

    private static EmittedComparisonState.Observation nothingArriving() {
        return copy(new ComparisonArrival.NothingArrives(), List.of());
    }

    private static int copies;

    private static EmittedComparisonState.Observation copy(ComparisonArrival arrival,
                                                           List<WhatMayStopARun> stops) {
        int at = copies++;
        return new EmittedComparisonState.Observation(
                ConstructOccurrence.asWritten(new SourceConstructOrigin(
                        new WrittenOwner.Body("m", "f"), at, 0, SourceConstruct.BINARY)),
                Numberings.comparison(1, 0), arrival, stops);
    }

    @Test
    void aCopyNothingGetsToShowsNothingOfTheWayToTheLine() {
        assertEquals(PAST_A_PRODUCT, GuardThresholds.stopsBefore(
                List.of(arrivingPast(PAST_A_PRODUCT), nothingArriving())).written());
        assertEquals(PAST_A_PRODUCT, GuardThresholds.stopsBefore(
                List.of(nothingArriving(), arrivingPast(PAST_A_PRODUCT))).written());
    }

    @Test
    void aCopyARunGetsToWithEverythingOnTheWayReadIsAWayToTheLineThatIsAllRead() {
        assertEquals(List.of(), GuardThresholds.stopsBefore(
                List.of(arrivingPast(PAST_A_PRODUCT), arrivingPast(List.of()))).written());
    }

    /** Each kind once, in the order a report names them in. */
    @Test
    void whatMayStopOnTheWayToEachCopyIsEachSaidOnce() {
        assertEquals(List.of(new WhatMayStopARun.AnOperator(), new WhatMayStopARun.ACall()),
                GuardThresholds.stopsBefore(List.of(
                        arrivingPast(List.of(new WhatMayStopARun.ACall())),
                        arrivingPast(PAST_A_PRODUCT))).written());
    }
}
