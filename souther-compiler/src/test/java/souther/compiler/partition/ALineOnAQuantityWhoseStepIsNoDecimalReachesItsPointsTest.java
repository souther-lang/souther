package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.BehaviorContract;
import souther.compiler.check.Carrier;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.PartId;
import souther.compiler.check.RuleRef;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Towards;

import java.math.BigInteger;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A border on a quantity whose own step is no decimal names both its points.
 *
 * <p><b>The geometry and not one type in it.</b> {@code 1 / 3 * x} over whole {@code x} takes the
 * values a third apart, so a line at one has {@code 4/3} beside it — a level the quantity stands at
 * and no count is. {@link LevelSpace} answering that is half of what the border needs: the answer
 * travels to a point, and a reader that turned it into a place to compare it against what the rules
 * leave would stop there, on a value that does not exist rather than on anything the model said.
 *
 * <p>So the range comes up to the level. What the rules leave is written in what a carrier counts,
 * because it is read off the declarations; every count is a ratio, so lifting an end loses nothing,
 * while lowering the level loses the level. A fixture over {@link LevelSpace} alone cannot tell the
 * two apart, because the lowering is not there.
 *
 * <p>No model writes this quantity until the affine reading admits division. What the border does
 * with it is decided here all the same: the geometry is exact now, and a reading that is exact only
 * as far as the order it is on is one nothing downstream can correct.
 */
class ALineOnAQuantityWhoseStepIsNoDecimalReachesItsPointsTest {

    private static final Carrier WHOLE = new Carrier.Whole();

    private static NumericTerm.FromOnePosition x() {
        return new NumericTerm.ValueOf(TermPath.of("x"));
    }

    private static ExactRatio ratio(long over, long under) {
        return ExactRatio.of(BigInteger.valueOf(over), BigInteger.valueOf(under));
    }

    /** {@code 1 / 3 * x}, whose values are a third apart because {@code x}'s are whole. */
    private static BorderQuantity aThirdOfAWholeNumber() {
        TermOrders on = TermOrdersFixtures.itself(x(), WHOLE);
        return new BorderQuantity.OverAForm("f",
                new LinearForm<>(ExactRatio.ZERO, Map.of(x(), ratio(1, 3))),
                Map.of(x(), on));
    }

    /** The border {@code 1 / 3 * x <= 1} draws, inside whatever the rules leave. */
    private static Border lineAtOne(NumericDomain.Bounds within) {
        return Border.at(
                BoundaryTarget.at(aThirdOfAWholeNumber(), Level.OfTheQuantity.of(1)),
                new LineOrigin.EnsuresOrigin(
                        new WhichLine.OfAComparisonOfAPart(
                                new ClauseStatementId(
                                        new PartId<>(new RuleRef.Ensures(
                                                new BehaviorContract.RuleId(null, 0, 0, null),
                                                "line"), 0),
                                        0)),
                        new LineFacts(new ComparisonClaim.Cut(Towards.BELOW, true))),
                within);
    }

    /**
     * The level beside the line is the quantity's own, and the point is owed at it.
     *
     * <p>A third past one, which the border carries as the number it is. Read as a place on the way
     * to being compared against what the rules leave, this is where the reading stopped.
     */
    @Test
    void thePointBesideTheLineIsAtTheLevelTheQuantityTakes() {
        Border border = lineAtOne(new NumericDomain.Bounds(null, null));

        Criterion.AtTheLevel beside = assertInstanceOf(Criterion.AtTheLevel.class,
                border.demand(new DomainPoint.BesideTheLine(Towards.ABOVE)).criterion());

        assertEquals(new Level.OfTheQuantity(ratio(4, 3)), beside.at(),
                "a third past one is where this quantity stands next, and it stays that number");
    }

    /**
     * And what the rules leave is read against it without either of them being written down.
     *
     * <p>The range is in whole numbers because the position is; the level is a third past one. A
     * range stopping at one leaves nothing there and a range running to two does — and neither
     * answer can be reached by asking which whole number the level is.
     */
    @Test
    void whatTheRulesLeaveIsReadAgainstThatLevelAsANumber() {
        assertInstanceOf(PointAnswer.AtLine.class,
                lineAtOne(new NumericDomain.Bounds(null, Endpoint.inclusive(Count.of(2))))
                        .answer(new DomainPoint.BesideTheLine(Towards.ABOVE)),
                "a third past one is under two, so a row is owed there");

        assertEquals(new PointAnswer.NotOwed(NotOwedReason.THE_RULES_REFUSE_IT),
                lineAtOne(new NumericDomain.Bounds(null, Endpoint.inclusive(Count.of(1))))
                        .answer(new DomainPoint.BesideTheLine(Towards.ABOVE)),
                "and over one, so a range stopping there leaves it nowhere");
    }
}
