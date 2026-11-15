package souther.compiler.query;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import souther.compiler.check.Carrier;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.RuleReportAnchor;
import souther.compiler.check.RuleRef;
import souther.compiler.coverage.Numberings;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.AuthoredPointMapping;
import souther.compiler.meaning.Derivation;
import souther.compiler.meaning.WrittenLine;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Towards;
import souther.compiler.partition.AuthoredPlacement;
import souther.compiler.partition.Border;
import souther.compiler.partition.BorderQuantity;
import souther.compiler.partition.BoundaryTarget;
import souther.compiler.partition.DomainPoint;
import souther.compiler.partition.ElementsMetOn;
import souther.compiler.partition.Level;
import souther.compiler.partition.LineFacts;
import souther.compiler.partition.LineOrigin;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

import java.util.List;
import java.util.Optional;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A reading of an order stands to the author's order by where each holds, and not by which way the
 * reading's quantity faces the line.
 *
 * <p>{@code Int.abs(d) >= 2} has two lines on {@code current} for each piece of the step, one
 * where {@code d} is positive and one where it is negative. The comparison holds above the first
 * and below the second, and the quantity faces both of them the same way, so a facing turns the
 * sides of one of them to the author's other one. Where each holds is the same on every line the
 * comparison is drawn on, so a side of the reading is the author's side of the same truth: the
 * side the comparison holds on stands for the side it holds on, and the side it fails on for the
 * side it fails on.
 *
 * <p>Where the author singled a value out and did not write an order there is no side of its that
 * the comparison holds on, and the facing is what tells the sides apart.
 */
class ATwoOrdersTellTheirSidesApartByWhereEachHoldsTest {

    private static final Carrier WHOLE = new Carrier.Whole();

    record Case(ComparisonClaim.Cut drawn, ComparisonClaim.Cut authored,
                Derivation.AComparisonRead.Facing facing) {
        @Override
        public String toString() {
            return "drawn " + drawn + ", authored " + authored + ", facing " + facing;
        }
    }

    static Stream<Case> everyOrderAgainstEveryOrderWhateverTheFacing() {
        List<ComparisonClaim.Cut> orders = List.of(
                new ComparisonClaim.Cut(Towards.ABOVE, true),
                new ComparisonClaim.Cut(Towards.BELOW, true),
                new ComparisonClaim.Cut(Towards.ABOVE, false),
                new ComparisonClaim.Cut(Towards.BELOW, false));
        return orders.stream().flatMap(drawn -> orders.stream()
                .filter(authored -> authored.holdsAtTheValue() == drawn.holdsAtTheValue())
                .flatMap(authored -> Stream.of(Derivation.AComparisonRead.Facing.values())
                        .map(facing -> new Case(drawn, authored, facing))));
    }

    @ParameterizedTest
    @MethodSource("everyOrderAgainstEveryOrderWhateverTheFacing")
    void aSideOfTheReadingIsTheSideOfTheAuthorsWhereTheComparisonHoldsAsItDoes(Case each) {
        AuthoredPlacement.Placed placed = (AuthoredPlacement.Placed)
                border(each.drawn(), each.authored(), each.facing()).placement();
        for (DomainPoint point : Border.pointsOf(origin(each.drawn(), each.authored(),
                each.facing()))) {
            if (point.side() == null) {
                continue;
            }
            Towards expected = point.side() == each.drawn().satisfyingSide()
                    ? each.authored().satisfyingSide()
                    : each.authored().satisfyingSide().opposite();
            assertEquals(Optional.of(sameKindOn(point, expected)), placed.of(point),
                    () -> point + " of " + each);
        }
    }

    @Test
    void whereTheAuthorSingledTheValueOutTheFacingTellsTheSidesApart() {
        DomainPoint beside = new DomainPoint.BesideTheLine(Towards.BELOW);
        ComparisonClaim.Cut drawn = new ComparisonClaim.Cut(Towards.ABOVE, true);
        ComparisonClaim.Singled singled = new ComparisonClaim.Singled(true);
        assertEquals(Optional.of(new DomainPoint.BesideTheLine(Towards.BELOW)),
                singledOut(drawn, singled, Derivation.AComparisonRead.Facing.AS_WRITTEN)
                        .of(beside));
        assertEquals(Optional.of(new DomainPoint.BesideTheLine(Towards.ABOVE)),
                singledOut(drawn, singled, Derivation.AComparisonRead.Facing.TURNED)
                        .of(beside));
    }

    private AuthoredPlacement.Placed singledOut(ComparisonClaim.Cut drawn,
                                                ComparisonClaim.Singled authored,
                                                Derivation.AComparisonRead.Facing facing) {
        return (AuthoredPlacement.Placed) border(drawn, authored, facing).placement();
    }

    private static DomainPoint sameKindOn(DomainPoint point, Towards side) {
        return switch (point) {
            case DomainPoint.BesideTheLine _ -> new DomainPoint.BesideTheLine(side);
            case DomainPoint.InTheRegion _ -> new DomainPoint.InTheRegion(side);
            case DomainPoint.AtTheLine at -> at;
        };
    }

    private static LineOrigin origin(ComparisonClaim drawn, ComparisonClaim authored,
                                     Derivation.AComparisonRead.Facing facing) {
        SourceConstructOrigin wrote = new SourceConstructOrigin(
                new WrittenOwner.Body("example.weigh", "weigh"), 1, 0, SourceConstruct.BINARY);
        return new LineOrigin.ComparisonOrigin(
                new LineOrigin.ComparisonOrigin.Read(
                        new RuleRef.Comparison("weigh", wrote),
                        new ModelOccurrence(wrote, ExpansionLineage.ORIGINAL),
                        new RuleReportAnchor.ByTheModuleThatWroteIt(),
                        List.of(Numberings.comparison(1, 0)), ElementsMetOn.EVERY,
                        LineOrigin.NOTHING_ON_THE_WAY, Optional.empty(), Optional.empty()),
                Optional.empty(), new LineFacts(drawn),
                new AuthoredPointMapping.Proven(WrittenLine.THE_COMPARISON, authored, facing,
                        true));
    }

    private static Border border(ComparisonClaim drawn, ComparisonClaim authored,
                                 Derivation.AComparisonRead.Facing facing) {
        NumericTerm.ValueOf term = new NumericTerm.ValueOf(TermPath.of("current"));
        BoundaryTarget at = BoundaryTarget.at(new BorderQuantity.OfACoordinate("weigh", term,
                TermOrdersFixtures.itself(term, WHOLE)),
                new Level.OnACarrier(WHOLE, Count.of(100)));
        return Border.at(at, origin(drawn, authored, facing),
                new NumericDomain.Bounds(Endpoint.inclusive(Count.of(0)),
                        Endpoint.inclusive(Count.of(1000))));
    }
}
