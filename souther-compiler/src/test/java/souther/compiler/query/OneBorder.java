package souther.compiler.query;

import souther.compiler.check.BehaviorContract;
import souther.compiler.check.Carrier;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.PartId;
import souther.compiler.check.RuleRef;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Towards;
import souther.compiler.partition.AuthoredLine;
import souther.compiler.partition.Border;
import souther.compiler.partition.BorderQuantity;
import souther.compiler.partition.BoundaryTarget;
import souther.compiler.partition.ClauseStatementId;
import souther.compiler.partition.DerivedValue;
import souther.compiler.partition.Level;
import souther.compiler.partition.LineFacts;
import souther.compiler.partition.LineOrigin;
import souther.compiler.partition.WhichLine;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

import java.util.List;

/** One border, for a test that needs a value of that type and for which border it is is no part
 *  of what it is about. */
public final class OneBorder {

    private OneBorder() {
    }

    static Border border() {
        Carrier carrier = new Carrier.Whole();
        NumericTerm.ValueOf value = new NumericTerm.ValueOf(TermPath.of("x"));
        BoundaryTarget target = BoundaryTarget.at(
                new BorderQuantity.OfACoordinate("cap", value,
                        TermOrdersFixtures.itself(value, carrier)),
                new Level.OnACarrier(carrier, Count.of(100)));
        LineOrigin origin = new LineOrigin.EnsuresOrigin(
                new WhichLine.OfAComparisonOfAPart(new ClauseStatementId(new PartId<>(
                        new RuleRef.Ensures(new BehaviorContract.RuleId(null, 0, 0, null), "cap"),
                        0), 0)),
                new LineFacts(new ComparisonClaim.Cut(Towards.BELOW, true)));
        return Border.at(target, origin, new NumericDomain.Bounds(null, null));
    }

    /** One computation of a comparison a body wrote, read at one call. */
    public static DerivedValue derivedValue() {
        SourceConstructOrigin comparison = new SourceConstructOrigin(
                new WrittenOwner.Body("m", "b"), 0, 0, SourceConstruct.BINARY);
        AuthoredLine line = new AuthoredLine(
                new WhichLine.OfAComparison(new RuleRef.Comparison("b", comparison)),
                new LineFacts(new ComparisonClaim.Cut(Towards.BELOW, true)), List.of());
        return new DerivedValue(line, List.of(new ModelOccurrence(comparison,
                ExpansionLineage.ORIGINAL)));
    }
}
