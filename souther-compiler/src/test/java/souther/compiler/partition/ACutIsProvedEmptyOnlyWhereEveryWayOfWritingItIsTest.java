package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a cut comes to where every way of writing its numbers came to nothing.
 *
 * <p>The rules leaving one case of a sum nothing say nothing about another case, and a way the
 * search did not get to the end of may have had the values. So the cut is the model's proof only
 * where every way was proved, and otherwise it is a cut this compiler did not compose for — said in
 * the same words whichever order the ways were walked in.
 */
class ACutIsProvedEmptyOnlyWhereEveryWayOfWritingItIsTest {

    private static final OnTheWay.TakenIn CUT = new OnTheWay.TakenIn(
            new ConditionReportAnchor.WhereTheReadingMetIt("m", new ConditionOccurrence("f", 0)),
            new TakenConstraint.Affine(
                    LinearForm.atom(new NumericTerm.ValueOf(TermPath.of("r").then("deadline"))),
                    Rel.GE));

    private static final ReachabilityGap PROVED = new ReachabilityGap.ProvedImpossible(CUT);

    private static final ReachabilityGap STOPPED = new ReachabilityGap.Uncomposed(CUT,
            ReachabilityGap.Why.TheWalkForItsPositionsWasStopped.by(
                    Set.of(CompositionBudget.VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT), Set.of()));

    private static final ReachabilityGap FOUND_NOTHING = new ReachabilityGap.Uncomposed(CUT,
            new ReachabilityGap.Why.NoValueComposedForItsPositions());

    private static final ReachabilityGap TWO_AT_ONE = new ReachabilityGap.Uncomposed(CUT,
            new ReachabilityGap.Why.TwoNumbersAtOneLocation());

    @Test
    void everyWayProvedIsAProof() {
        assertEquals(PROVED, ReachabilityGap.overEveryWay(CUT, List.of(PROVED, PROVED), false));
    }

    @Test
    void aWayAFigureStoppedIsNotProvedBecauseAnotherWayWas() {
        assertEquals(STOPPED, ReachabilityGap.overEveryWay(CUT, List.of(PROVED, STOPPED), false));
        assertEquals(STOPPED, ReachabilityGap.overEveryWay(CUT, List.of(STOPPED, PROVED), false));
    }

    @Test
    void aWayThatFoundNothingIsNotProvedBecauseAnotherWayWas() {
        assertEquals(FOUND_NOTHING,
                ReachabilityGap.overEveryWay(CUT, List.of(PROVED, FOUND_NOTHING), false));
    }

    /** A way nothing was looked at in is not one shown to leave nothing. */
    @Test
    void everyWayLookedAtProvedIsNoProofWhereSomeWayWasNotLookedAt() {
        assertEquals(FOUND_NOTHING, ReachabilityGap.overEveryWay(CUT, List.of(PROVED), true));
        assertEquals(FOUND_NOTHING, ReachabilityGap.overEveryWay(CUT, List.of(), false));
    }

    /** What stopped the ways is said the same whichever of them was walked first. */
    @Test
    void theWordsDoNotDependOnTheOrderTheWaysWereWalkedIn() {
        assertEquals(STOPPED,
                ReachabilityGap.overEveryWay(CUT, List.of(TWO_AT_ONE, FOUND_NOTHING, STOPPED),
                        false));
        assertEquals(STOPPED,
                ReachabilityGap.overEveryWay(CUT, List.of(STOPPED, FOUND_NOTHING, TWO_AT_ONE),
                        false));
        assertEquals(TWO_AT_ONE,
                ReachabilityGap.overEveryWay(CUT, List.of(FOUND_NOTHING, TWO_AT_ONE), false));
        assertEquals(TWO_AT_ONE,
                ReachabilityGap.overEveryWay(CUT, List.of(TWO_AT_ONE, FOUND_NOTHING), false));
    }
}
