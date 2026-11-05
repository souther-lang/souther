package souther.compiler.query;

import org.junit.jupiter.api.Test;

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
import souther.compiler.partition.AxisId;
import souther.compiler.partition.Border;
import souther.compiler.partition.BorderObligationPoint;
import souther.compiler.partition.BorderQuantity;
import souther.compiler.partition.BoundaryTarget;
import souther.compiler.partition.DomainPoint;
import souther.compiler.partition.ElementsMetOn;
import souther.compiler.partition.Level;
import souther.compiler.partition.LineFacts;
import souther.compiler.partition.LineOrigin;
import souther.compiler.partition.OwedPoint;
import souther.compiler.partition.ReadingSeat;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A reading shown to be a place of the author's line whose sides it cannot tell apart is about
 * every point of the author's line of the kind it cannot tie, and the gate a search is made under
 * ({@link Coverages#reachesAPointNoRowMeets}) asks it to be searched where any of them is unmet.
 *
 * <p>The comparison here keeps the values from a hundred up and was written as singling a value out:
 * the reading's line at a hundred is the author's line at it, and a side of the reading's is no
 * side of a line that names a value, so its run beside the line stands to both of the author's
 * ({@link ReadingSeat.Untied}). What a row there shows is said against both, and is worth showing
 * while either is unmet.
 *
 * <p>Asked of the gate and of a border made here rather than of a model's search: no model this
 * compiler reads yet comes to an untied reading, and the gate is what the search is made under for
 * every reading alike.
 */
class TheGateReadsAnUntiedReadingAsAboutEveryPointItCannotTieTest {

    private static final Carrier WHOLE = new Carrier.Whole();

    @Test
    void theRunBesideTheLineIsAboutBothOfTheAuthorsRunsAndTiedToNeither() {
        Border reading = untied();
        assertTrue(reading.placement() instanceof AuthoredPlacement.Placed,
                () -> "the reading is a place of the author's line: " + reading.placement());
        List<OwedPoint> about = reading.about(besideTheLine(reading));
        assertEquals(2, about.size(), () -> "one point of each side: " + about);
        for (OwedPoint each : about) {
            assertTrue(each.seat() instanceof ReadingSeat.Untied,
                    () -> "neither is tied: " + each.seat());
        }
    }

    @Test
    void itIsToBeSearchedWhereEitherIsUnmetAndNotWhereBothAreMet() {
        Border reading = untied();
        DomainPoint beside = besideTheLine(reading);
        List<BorderObligationPoint> sides =
                reading.about(beside).stream().map(OwedPoint::point).toList();
        assertTrue(Coverages.reachesAPointNoRowMeets(reading, beside, Set.copyOf(sides)),
                "both unmet");
        assertTrue(Coverages.reachesAPointNoRowMeets(reading, beside, Set.of(sides.get(0))),
                "the first alone unmet");
        assertTrue(Coverages.reachesAPointNoRowMeets(reading, beside, Set.of(sides.get(1))),
                "the second alone unmet");
        assertFalse(Coverages.reachesAPointNoRowMeets(reading, beside, Set.of()),
                "both met, or kept by nobody here");
    }

    /** The reading's own point beside its line, which a comparison keeping one side has one of. */
    private static DomainPoint besideTheLine(Border reading) {
        List<DomainPoint> beside = Border.pointsOf(reading.origin()).stream()
                .filter(DomainPoint.BesideTheLine.class::isInstance).toList();
        assertEquals(1, beside.size(), () -> "one point beside the line: " + beside);
        return beside.getFirst();
    }

    /** A comparison at a hundred kept above, read where the author singled the value out. */
    private static Border untied() {
        AxisId axis = new AxisId("weigh", "w.a");
        NumericTerm.ValueOf term = new NumericTerm.ValueOf(TermPath.of(axis.term()));
        BoundaryTarget at = BoundaryTarget.at(new BorderQuantity.OfACoordinate(axis.behavior(),
                term, TermOrdersFixtures.itself(term, WHOLE)),
                new Level.OnACarrier(WHOLE, Count.of(100)));
        SourceConstructOrigin wrote = new SourceConstructOrigin(
                new WrittenOwner.Body("example.weigh", "weigh"), 1, 0, SourceConstruct.BINARY);
        LineOrigin origin = new LineOrigin.ComparisonOrigin(
                new LineOrigin.ComparisonOrigin.Read(
                        new RuleRef.Comparison("weigh", wrote),
                        new ModelOccurrence(wrote, ExpansionLineage.ORIGINAL),
                        new RuleReportAnchor.ByTheModuleThatWroteIt(),
                        List.of(Numberings.comparison(1, 0)), ElementsMetOn.EVERY,
                        LineOrigin.NOTHING_ON_THE_WAY, Optional.empty(), Optional.empty()),
                Optional.empty(),
                new LineFacts(new ComparisonClaim.Cut(Towards.ABOVE, true)),
                new AuthoredPointMapping.Proven(WrittenLine.THE_COMPARISON,
                        new ComparisonClaim.Singled(true),
                        Derivation.AComparisonRead.Facing.NOTHING_WRITTEN, false));
        return Border.at(at, origin, new NumericDomain.Bounds(Endpoint.inclusive(Count.of(0)),
                Endpoint.inclusive(Count.of(1000))));
    }
}
