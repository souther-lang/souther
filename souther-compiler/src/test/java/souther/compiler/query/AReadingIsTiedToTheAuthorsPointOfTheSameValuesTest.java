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
 * A point of a reading is the point of its author's line that is at the same values.
 *
 * <p>The author's quantity is {@code q}, and the reading is on {@code x}, with
 * {@code q = x} or {@code q = 3 - x}: the same cut of the integers, between the values 1 and 2 of
 * either, which is how {@code Int.abs(d) >= 2} is read through each of its arms. An order names the
 * number it is at as one of the classes either side of the cut, and a relation and its denial name
 * the two numbers beside it, so a reading and its author's line may be at different numbers of the
 * one cut. What is asked here is the values: the point of the author's line a value of {@code x} is,
 * worked out from {@code q} at that value, with no use of what either line claims of its sides.
 */
class AReadingIsTiedToTheAuthorsPointOfTheSameValuesTest {

    private static final Carrier WHOLE = new Carrier.Whole();

    /** @param turned whether {@code q} falls where {@code x} rises */
    record Case(boolean turned, ComparisonClaim.Cut authored, ComparisonClaim.Cut drawn) {
        long q(long x) {
            return turned ? 3 - x : x;
        }

        /** The number the author's line is at, which is the one its class begins at. */
        long authorsNumber() {
            return authored.valueBelongs() == Towards.ABOVE ? 2 : 1;
        }

        /** The number the reading is at. */
        long readingsNumber() {
            return drawn.valueBelongs() == Towards.ABOVE ? 2 : 1;
        }

        /** The author's point that a value of {@code x} is, as {@code q} at it says. */
        DomainPoint authorsPointAt(long x) {
            long q = q(x);
            Towards beyond = authored.valueBelongs().opposite();
            if (q == authorsNumber()) {
                return new DomainPoint.AtTheLine();
            }
            if (q == authorsNumber() + (beyond == Towards.ABOVE ? 1 : -1)) {
                return new DomainPoint.BesideTheLine(beyond);
            }
            return new DomainPoint.InTheRegion(q >= 2 ? Towards.ABOVE : Towards.BELOW);
        }

        @Override
        public String toString() {
            return (turned ? "q = 3 - x" : "q = x") + ", author " + authored + ", reading " + drawn;
        }
    }

    static Stream<Case> everyWayTheTwoLinesNameTheirNumbers() {
        List<ComparisonClaim.Cut> orders = List.of(
                new ComparisonClaim.Cut(Towards.ABOVE, true),
                new ComparisonClaim.Cut(Towards.ABOVE, false),
                new ComparisonClaim.Cut(Towards.BELOW, true),
                new ComparisonClaim.Cut(Towards.BELOW, false));
        return Stream.of(false, true).flatMap(turned -> orders.stream()
                .flatMap(authored -> orders.stream()
                        .map(drawn -> new Case(turned, authored, drawn))));
    }

    @ParameterizedTest
    @MethodSource("everyWayTheTwoLinesNameTheirNumbers")
    void theNumberTheReadingIsAtIsThePointTheAuthorsLineHasThere(Case each) {
        Border reading = border(each.drawn(), each.authored(), facingOf(each.turned()),
                each.readingsNumber());
        AuthoredPlacement.Placed placed = (AuthoredPlacement.Placed) reading.placement();
        assertEquals(Optional.of(each.authorsPointAt(each.readingsNumber())),
                placed.of(new DomainPoint.AtTheLine()), "at the number the reading names");
        Towards beyondTheReadings = each.drawn().valueBelongs().opposite();
        assertEquals(Optional.of(each.authorsPointAt(each.readingsNumber()
                        + (beyondTheReadings == Towards.ABOVE ? 1 : -1))),
                placed.of(new DomainPoint.BesideTheLine(beyondTheReadings)),
                "beside the number the reading names");
    }

    @ParameterizedTest
    @MethodSource("everyWayTheTwoLinesNameTheirNumbers")
    void aRegionOfTheReadingIsTheRegionOfTheAuthorsThatItsValuesAreIn(Case each) {
        Border reading = border(each.drawn(), each.authored(), facingOf(each.turned()),
                each.readingsNumber());
        AuthoredPlacement.Placed placed = (AuthoredPlacement.Placed) reading.placement();
        assertEquals(Optional.of(each.authorsPointAt(5)),
                placed.of(new DomainPoint.InTheRegion(Towards.ABOVE)));
        assertEquals(Optional.of(each.authorsPointAt(-3)),
                placed.of(new DomainPoint.InTheRegion(Towards.BELOW)));
    }

    @Test
    void whereTheAuthorSingledTheValueOutTheFacingTellsTheSidesApart() {
        ComparisonClaim.Cut drawn = new ComparisonClaim.Cut(Towards.ABOVE, true);
        ComparisonClaim.Singled singled = new ComparisonClaim.Singled(true);
        DomainPoint beside = new DomainPoint.BesideTheLine(Towards.BELOW);
        assertEquals(Optional.of(new DomainPoint.BesideTheLine(Towards.BELOW)),
                ((AuthoredPlacement.Placed) border(drawn, singled,
                        Derivation.AComparisonRead.Facing.AS_WRITTEN, 2).placement()).of(beside));
        assertEquals(Optional.of(new DomainPoint.BesideTheLine(Towards.ABOVE)),
                ((AuthoredPlacement.Placed) border(drawn, singled,
                        Derivation.AComparisonRead.Facing.TURNED, 2).placement()).of(beside));
    }

    private static Derivation.AComparisonRead.Facing facingOf(boolean turned) {
        return turned ? Derivation.AComparisonRead.Facing.TURNED
                : Derivation.AComparisonRead.Facing.AS_WRITTEN;
    }

    private static Border border(ComparisonClaim drawn, ComparisonClaim authored,
                                 Derivation.AComparisonRead.Facing facing, long at) {
        SourceConstructOrigin wrote = new SourceConstructOrigin(
                new WrittenOwner.Body("example.weigh", "weigh"), 1, 0, SourceConstruct.BINARY);
        LineOrigin origin = new LineOrigin.ComparisonOrigin(
                new LineOrigin.ComparisonOrigin.Read(
                        new RuleRef.Comparison("weigh", wrote),
                        new ModelOccurrence(wrote, ExpansionLineage.ORIGINAL),
                        new RuleReportAnchor.ByTheModuleThatWroteIt(),
                        List.of(Numberings.comparison(1, 0)), ElementsMetOn.EVERY,
                        LineOrigin.NOTHING_ON_THE_WAY, Optional.empty(), Optional.empty()),
                Optional.empty(), new LineFacts(drawn),
                new AuthoredPointMapping.Proven(WrittenLine.THE_COMPARISON, authored, facing,
                        true));
        NumericTerm.ValueOf term = new NumericTerm.ValueOf(TermPath.of("x"));
        BoundaryTarget target = BoundaryTarget.at(new BorderQuantity.OfACoordinate("weigh", term,
                TermOrdersFixtures.itself(term, WHOLE)),
                new Level.OnACarrier(WHOLE, Count.of(at)));
        return Border.at(target, origin, new NumericDomain.Bounds(
                Endpoint.inclusive(Count.of(-10)), Endpoint.inclusive(Count.of(10))));
    }
}
