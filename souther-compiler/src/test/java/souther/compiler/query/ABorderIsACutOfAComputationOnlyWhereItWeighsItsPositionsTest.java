package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.RuleReportAnchor;
import souther.compiler.check.RuleRef;
import souther.compiler.coverage.Numberings;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.AuthoredPointMapping;
import souther.compiler.meaning.Derivation;
import souther.compiler.meaning.WrittenLine;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Towards;
import souther.compiler.partition.Border;
import souther.compiler.partition.BorderQuantity;
import souther.compiler.partition.BoundaryTarget;
import souther.compiler.partition.DerivedValue;
import souther.compiler.partition.ElementsMetOn;
import souther.compiler.partition.Level;
import souther.compiler.partition.LineFacts;
import souther.compiler.partition.LineOrigin;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison read at one call can be cut on a value derived from several positions and on one
 * position at once: {@code gradeOf(a + b)} against an input is read once per piece of
 * {@code gradeOf}, and in a piece the value is a constant, so the line is on the input alone.
 *
 * <p>The computation is the weighing of the positions, and a line on one of them says nothing of
 * it. Both borders are of the same comparison at the same call, so which of them the computation is
 * cut by is the quantity's to say; every reader of the computation's borders asks the computation,
 * and none of them has to remember the second condition.
 */
class ABorderIsACutOfAComputationOnlyWhereItWeighsItsPositionsTest {

    private static final Carrier WHOLE = new Carrier.Whole();
    private static final NumericTerm.ValueOf A = new NumericTerm.ValueOf(TermPath.of("a"));
    private static final NumericTerm.ValueOf B = new NumericTerm.ValueOf(TermPath.of("b"));

    @Test
    void aLineOnTheSumOfTwoPositionsIsACutOfTheComputationAtTheCallItIsReadAt() {
        Border onTheSum = border(sumOfTwo(), call(1));
        assertTrue(computationOf(onTheSum).isCutBy(onTheSum, call(1)));
    }

    @Test
    void aLineOfTheSameComparisonAtTheSameCallOnOnePositionIsNot() {
        Border onTheSum = border(sumOfTwo(), call(1));
        Border onOnePosition = border(onePosition(), call(1));
        assertFalse(computationOf(onTheSum).isCutBy(onOnePosition, call(1)),
                "the same comparison and the same call, on a value that is one position");
    }

    @Test
    void aLineOnTheSumIsStillNotACutOfTheComputationAtAnotherCall() {
        Border onTheSum = border(sumOfTwo(), call(1));
        assertFalse(computationOf(onTheSum).isCutBy(border(sumOfTwo(), call(2)), call(2)),
                "the call is not one the computation was read at");
    }

    private static DerivedValue computationOf(Border border) {
        return new DerivedValue(border.origin().authoredLine(),
                border.origin().readAt().inOrder());
    }

    private static ModelOccurrence call(int at) {
        return new ModelOccurrence(wrote(at), ExpansionLineage.ORIGINAL);
    }

    private static SourceConstructOrigin wrote(int at) {
        return new SourceConstructOrigin(
                new WrittenOwner.Body("example.weigh", "weigh"), at, 0, SourceConstruct.BINARY);
    }

    private static BorderQuantity sumOfTwo() {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(A, ExactRatio.of(1));
        coefs.put(B, ExactRatio.of(1));
        Map<NumericTerm, TermOrders> on = new LinkedHashMap<>();
        on.put(A, TermOrdersFixtures.itself(A, WHOLE));
        on.put(B, TermOrdersFixtures.itself(B, WHOLE));
        return new BorderQuantity.OverAForm("weigh", new LinearForm<>(ExactRatio.ZERO, coefs), on);
    }

    private static BorderQuantity onePosition() {
        return new BorderQuantity.OfACoordinate("weigh", A, TermOrdersFixtures.itself(A, WHOLE));
    }

    /** A line of the comparison written at line 1, read at the call {@code readAt}. */
    private static Border border(BorderQuantity of, ModelOccurrence readAt) {
        SourceConstructOrigin comparison = wrote(1);
        LineOrigin origin = new LineOrigin.ComparisonOrigin(
                new LineOrigin.ComparisonOrigin.Read(
                        new RuleRef.Comparison("weigh", comparison), readAt,
                        new RuleReportAnchor.ByTheModuleThatWroteIt(),
                        List.of(Numberings.comparison(1, 0)), ElementsMetOn.EVERY,
                        LineOrigin.NOTHING_ON_THE_WAY, Optional.empty(), Optional.empty()),
                Optional.empty(),
                new LineFacts(new ComparisonClaim.Cut(Towards.ABOVE, true)),
                new AuthoredPointMapping.Proven(WrittenLine.THE_COMPARISON,
                        new ComparisonClaim.Cut(Towards.ABOVE, true),
                        Derivation.AComparisonRead.Facing.AS_WRITTEN, true));
        Level at = of instanceof BorderQuantity.OfACoordinate
                ? new Level.OnACarrier(WHOLE, Count.of(100)) : Level.OfTheQuantity.of(100);
        return Border.at(BoundaryTarget.at(of, at), origin,
                new NumericDomain.Bounds(Endpoint.inclusive(Count.of(0)),
                        Endpoint.inclusive(Count.of(1000))));
    }
}
