package souther.compiler.query;

import souther.compiler.check.BehaviorContract;
import souther.compiler.check.Carrier;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.RuleRef;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Towards;
import souther.compiler.partition.Border;
import souther.compiler.partition.BorderQuantity;
import souther.compiler.partition.BoundaryTarget;
import souther.compiler.partition.Level;
import souther.compiler.partition.LineFacts;
import souther.compiler.partition.LineOrigin;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Borders to put the question of the lines beside them to, written rather than compiled.
 *
 * <p>What these are about is which answer a border's own shape earns — a line over two positions, a
 * line over one, and a rule that names a value rather than ordering the values around it. A model
 * that produces each of those is three models and a paragraph apiece about why they produce it;
 * written here, the shape is the whole of what the fixture says.
 *
 * <p>The third of them is one no reading of a model produces today: a rule that names a value over
 * an arithmetic form draws no line at all, so nothing reaches the answer that says this compiler
 * has no strategy for it. It is written here because the answer is about a strategy rather than
 * about the model — the day a form equality draws a line, what it comes back as is decided by the
 * rule these hold, and not by whichever arm was nearest.
 */
final class TheLinesBesideABorder {

    private static final Carrier WHOLE = new Carrier.Whole();

    private static final NumericTerm.ValueOf X = new NumericTerm.ValueOf(TermPath.of("x"));

    private static final NumericTerm.ValueOf Y = new NumericTerm.ValueOf(TermPath.of("y"));

    private TheLinesBesideABorder() {}

    /** {@code y <= 2 * x}, which runs along {@code -2 * x + y} and has lines one step from it. */
    static Border aLineOverTwoPositions() {
        return over(ordered(), form());
    }

    /** The same quantity, cut by a rule that names a value instead of ordering the values. */
    static Border aBorderThatNamesAValue() {
        return over(new LineFacts(new ComparisonClaim.Singled(true)), form());
    }

    /** A bound on one position, which is the same line weighed one more and nothing weighed one
     *  less. */
    static Border aBoundOnOnePosition() {
        return over(ordered(), new BorderQuantity.OfACoordinate("f", X,
                TermOrdersFixtures.itself(X, WHOLE)));
    }

    /** What the rows are weighed by: {@code x} at minus two and {@code y} at one. */
    private static BorderQuantity form() {
        Map<NumericTerm, BigDecimal> weights = new LinkedHashMap<>();
        weights.put(X, BigDecimal.valueOf(-2));
        weights.put(Y, BigDecimal.ONE);
        Map<NumericTerm, souther.compiler.inputs.TermOrders> on = new LinkedHashMap<>();
        on.put(X, TermOrdersFixtures.itself(X, WHOLE));
        on.put(Y, TermOrdersFixtures.itself(Y, WHOLE));
        return new BorderQuantity.OverAForm("f", new LinearForm<>(BigDecimal.ZERO, weights), on);
    }

    private static LineFacts ordered() {
        return new LineFacts(new ComparisonClaim.Cut(Towards.BELOW, true));
    }

    private static Border over(LineFacts facts, BorderQuantity of) {
        BoundaryTarget target = BoundaryTarget.at(of,
                of instanceof BorderQuantity.OverAForm
                        ? new Level.ACount(Count.of(0))
                        : new Level.OnACarrier(WHOLE, Count.of(0)));
        LineOrigin origin = new LineOrigin.EnsuresOrigin(
                new souther.compiler.partition.WhichLine.OfAComparisonOfAPart(
                        new souther.compiler.partition.ClauseStatementId(
                                new souther.compiler.check.PartId<>(new RuleRef.Ensures(
                                        new BehaviorContract.RuleId(null, 0, 0, null), "line"), 0),
                                0)),
                facts);
        return Border.at(target, origin, new NumericDomain.Bounds(null, null));
    }
}
