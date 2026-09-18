package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.BehaviorContract;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.Carrier;
import souther.compiler.check.PartId;
import souther.compiler.check.RuleRef;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * Which points a line has, and which order a reader is walked through them.
 *
 * <p>Two answers, and they were one value. The points came back as a set, which is what the
 * question "which points does this line have" wants; the order they were sorted into was read off
 * that same value by everything that shows a border's points in turn. A set's equality does not see
 * an order, so the two arrangements were one answer and nothing downstream could have disagreed
 * with a walk that had them the other way round.
 *
 * <p>The order is the answer now, and a sequence's equality sees it. What is left of the other
 * question is asked of the points rather than of their order: that a border answers at each of them
 * and at no other. The uniqueness the set used to carry is asked here too, because the type no
 * longer carries it.
 */
class WhichPointsALineHasAndWhichOrderTheyAreWalkedInAreTwoAnswersTest {

    private static final Carrier WHOLE = new Carrier.Whole();
    private static final NumericTerm.ValueOf X = new NumericTerm.ValueOf(TermPath.of("x"));

    /**
     * A line names each of its points once, whichever kind of rule drew it.
     *
     * <p>Both shapes a claim can be, because the points are built by a switch over them and a shape
     * that named one of its points twice would be answering at the same place twice. Held by the
     * set this used to come back as; nothing holds it now but this.
     */
    @Test
    void everyPointALineHasIsNamedOnce() {
        for (ComparisonClaim claim : List.of(
                new ComparisonClaim.Cut(souther.compiler.numeric.Towards.BELOW, true),
                new ComparisonClaim.Singled(true))) {
            List<DomainPoint> points = Border.pointsOf(originOf(claim));
            assertEquals(points.size(), new HashSet<>(points).size(),
                    "a line names each of its points once: " + points);
        }
    }

    /**
     * The points come back as a sequence, and two arrangements of them are two answers.
     *
     * <p>This is the whole of the disposition. Answered as a set, the two would compare equal and a
     * reader taking an order off one of them would have been reading something no equality could
     * tell from its opposite. A later edit putting the answer back into a set does not fail here —
     * it fails to compile here, which is the same red said earlier.
     */
    @Test
    void thePointsAreAnsweredAsASequenceWhoseEqualitySeesTheOrder() {
        List<DomainPoint> points = Border.pointsOf(originOf(new ComparisonClaim.Singled(true)));
        List<DomainPoint> theOtherWayRound = new ArrayList<>(points);
        Collections.reverse(theOtherWayRound);

        assertNotEquals(List.copyOf(theOtherWayRound), points,
                "two arrangements of one line's points are two answers");
        assertEquals(new HashSet<>(theOtherWayRound), new HashSet<>(points),
                "and they are arrangements of the same points, which is the other question");
    }

    /**
     * A border is total whatever order its answers were built in, and is walked in the line's.
     *
     * <p>The check that a border answers everywhere reads which points it answers at and not which
     * order they were put in, so a branch that filled them in some other order builds the same
     * border. What a reader is walked through is the line's order either way, and that is what the
     * constructor puts them back into.
     */
    @Test
    void aBorderIsTotalWhateverOrderItsAnswersWereBuiltIn() {
        Border asBuilt = aBorder();
        List<DomainPoint> backwards = new ArrayList<>(asBuilt.answers().keySet());
        Collections.reverse(backwards);

        Map<DomainPoint, PointAnswer> filledBackwards = new LinkedHashMap<>();
        for (DomainPoint point : backwards) {
            filledBackwards.put(point, asBuilt.answer(point));
        }
        Border rebuilt = new Border(asBuilt.cut(), asBuilt.origin(), filledBackwards);

        assertEquals(Border.pointsOf(asBuilt.origin()),
                List.copyOf(rebuilt.answers().keySet()),
                "a border is walked through its line's points in the line's order");
        assertEquals(asBuilt, rebuilt,
                "and a border filled in some other order is the same border");
    }

    private static Border aBorder() {
        return Border.at(BoundaryTarget.at(
                        new BorderQuantity.OfACoordinate("f", X,
                                TermOrdersFixtures.itself(X, WHOLE)),
                        new Level.OnACarrier(WHOLE, Count.of(0))),
                originOf(new ComparisonClaim.Singled(true)),
                new NumericDomain.Bounds(null, null));
    }

    private static LineOrigin originOf(ComparisonClaim claim) {
        return new LineOrigin.EnsuresOrigin(
                new WhichLine.OfAComparisonOfAPart(
                        new ClauseStatementId(
                                new PartId<>(new RuleRef.Ensures(
                                        new BehaviorContract.RuleId(null, 0, 0, null), "line"), 0),
                                0)),
                new LineFacts(claim));
    }
}
