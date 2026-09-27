package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.check.Carrier;
import souther.compiler.inputs.NameReach;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.regex.PatternPlan;
import souther.compiler.values.ValueSet;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A pair held a distance apart that this compiler cannot add to any place it tries says so, beside
 * the figure the walk along the line met.
 *
 * <p>Two whole numbers a fine decimal apart. The walk along the line takes whole places and meets its
 * figure, as a walk over a line nothing bounds does; at each place it takes, the other position is
 * worked out by adding the distance, and a whole number plus a decimal of a scale near the end of the
 * range is a number no run of this compiler holds. Both of those left the pair unsettled, and what
 * a reader does about them differs — raise the figure, or nothing — so both are said.
 */
class APairAtADistanceThisCannotHoldSaysSoBesideItsFigureTest {

    private static final NumericTerm.FromOnePosition ON =
            new NumericTerm.ValueOf(TermPath.of("on"));

    private static final NumericTerm.FromOnePosition AGAINST =
            new NumericTerm.ValueOf(TermPath.of("against"));

    /** A tenth to the power of a scale near the end of the range. */
    private static final ExactRatio FINE = ExactRatio.of(new BigDecimal(BigInteger.ONE, 1 << 30));

    @Test
    void theFigureAndTheDistanceNotHeldAreBothSaid() {
        Realization.Unknown left = assertInstanceOf(Realization.Unknown.class,
                pairAt(FINE), "nothing is composed where no place is held");

        assertEquals(Set.of(new CompositionCapacity(
                        CompositionCapacity.Where.PLACES_A_DISTANCE_MOVES_A_POSITION_TO,
                        UnheldNumber.NO_REPRESENTATION_EXISTS)),
                left.unheld(), "the distance could not be added, and no run adds it");
        assertEquals(Set.of(CompositionBudget.PLACES_A_PAIR_IS_TRIED_AT), left.stoppedBy(),
                "and the walk along the line met its figure");
        assertEquals(Realization.Unknown.Reason.NOTHING_COMPOSED_ONE, left.why(),
                "with the word the figure comes back with");
    }

    /** And a distance this can add composes the pair, which is the control. */
    @Test
    void aDistanceThisCanAddComposesThePair() {
        assertInstanceOf(Realization.Found.class, pairAt(ExactRatio.ONE));
    }

    private static Realization pairAt(ExactRatio apart) {
        WitnessSearch any = new WitnessSearch(
                AdmittedValues.of(Map.of(ON.position(), ValueSet.ANY,
                        AGAINST.position(), ValueSet.ANY), NameReach.NONE),
                PatternPlan.Budget.OF_A_WITNESS::meter);
        return new LevelRealizer().realize(
                new Standing.OfTwoOnOneCarrier(ON, AGAINST, new Carrier.Whole(),
                        new Criterion.AtTheLevel(new Level.OfTheQuantity(apart))),
                NothingTheRulesSay.REGION, any);
    }
}
