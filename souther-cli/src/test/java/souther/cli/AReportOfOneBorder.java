package souther.cli;

import souther.compiler.query.WeakeningSet;
import souther.compiler.query.Weakening;
import souther.compiler.query.Measurement;
import souther.compiler.check.Carrier;
import souther.compiler.check.Clause;
import souther.compiler.check.ClauseName;
import souther.compiler.check.RuleRef;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.partition.AxisId;
import souther.compiler.partition.Border;
import souther.compiler.partition.BorderQuantity;
import souther.compiler.partition.BoundaryTarget;
import souther.compiler.partition.Demand;
import souther.compiler.partition.OriginRef;
import souther.compiler.partition.PointRole;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.ItemAssessment;
import souther.compiler.query.PartitionDerivation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;
import souther.compiler.source.SourceId;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.EnumMap;
import java.util.List;
import java.util.function.Function;

/**
 * A report of one behavior whose partition is one border, written from the evidence.
 *
 * <p>Shared because two tests ask what a verdict makes of a border and each would otherwise carry
 * its own way of building one. Two fixtures for one shape is two things to keep in step, and the
 * one that was not kept would be a test asserting a verdict about a border the report no longer
 * builds that way.
 *
 * <p>Written from the evidence rather than from a source on purpose: what these are about is what a
 * verdict does with a point that came to an answer and one that did not, and a model that produces
 * that pair says less about it than these fifteen lines do.
 */
final class AReportOfOneBorder {

    private AReportOfOneBorder() {}

    /** A bound at 100 over a position the rules run from 1 to 1000, so all four points are owed. */
    static Border aBoundedBorder() {
        OriginRef origin = new OriginRef.InvariantOrigin(new RuleRef.Invariant(new Clause.Ref(
                new Clause.Id(TypeSymbols.declared(new TypeKey("example.rate", "Amount")), 0),
                java.util.Optional.of(new ClauseName("cap")))), 0, true);
        return Border.at(
                BoundaryTarget.at(
                        new BorderQuantity.OfACoordinate(new AxisId("weigh", "w.a"),
                                new NumericTerm.ValueOf(TermPath.of("w").then("a")),
                                souther.compiler.inputs.TermOrders.itself(Carrier.WHOLE)),
                        new souther.compiler.partition.Level.OnACarrier(Carrier.WHOLE,
                                Count.of(100))),
                origin,
                new NumericDomain.Bounds(Endpoint.inclusive(Count.of(1)),
                        Endpoint.inclusive(Count.of(1000))));
    }

    /** The same border a rule leaves at 100 and up, where the ON point is the whole of what it owes. */
    static Border aBorderAtTheEdgeOfItsDomain() {
        OriginRef origin = new OriginRef.InvariantOrigin(new RuleRef.Invariant(new Clause.Ref(
                new Clause.Id(TypeSymbols.declared(new TypeKey("example.rate", "Amount")), 0),
                java.util.Optional.of(new ClauseName("cap")))), 0, true);
        return Border.at(
                BoundaryTarget.at(
                        new BorderQuantity.OfACoordinate(new AxisId("weigh", "w.a"),
                                new NumericTerm.ValueOf(TermPath.of("w").then("a")),
                                souther.compiler.inputs.TermOrders.itself(Carrier.WHOLE)),
                        new souther.compiler.partition.Level.OnACarrier(Carrier.WHOLE,
                                Count.of(100))),
                origin,
                new NumericDomain.Bounds(Endpoint.inclusive(Count.of(100)), null));
    }

    /** A point measured to the end, whichever way it came out. */
    static Measurement<ItemAssessment.Coverage> settled(ItemAssessment.Coverage verdict) {
        return new Measurement.Complete<>(verdict);
    }

    /** A point whose reading was not whole, so what it did not find is undecided rather than
     *  absent. What weakened it is a row that never finished. */
    static Measurement<ItemAssessment.Coverage> undecided() {
        return new Measurement.Partial<>(new ItemAssessment.Coverage.NoHit(),
                WeakeningSet.of(new Weakening.ObservationIncomplete(
                        new souther.compiler.observe.Incompleteness(
                                souther.compiler.observe.Incompleteness.Code.ROW_UNDECIDED,
                                new souther.compiler.observe.Target.OfRow(
                                        new souther.compiler.observe.RowRef("take",
                                                new souther.compiler.source.SourceId("0"),
                                                new souther.compiler.observe.RowIdentity.Unnamed(1))),
                                java.util.Optional.empty()))));
    }

    /**
     * {@code border} assessed point by point, with {@code coverage} saying what each point came to.
     *
     * <p>A point the border does not owe is not one a coverage answer is invented for: what it is,
     * is not owed, and a fixture saying anything else about it would be describing a border other
     * than the one handed in.
     */
    static BorderAssessment assessed(Border border,
                                     Function<PointRole, Measurement<ItemAssessment.Coverage>>
                                             coverage) {
        EnumMap<PointRole, ItemAssessment> items = new EnumMap<>(PointRole.class);
        for (PointRole role : PointRole.values()) {
            if (border.demand(role) instanceof Demand.NotOwed not) {
                items.put(role, new ItemAssessment.NotOwed(not.reason()));
                continue;
            }
            // Proven by the rules, which is the one way of being writable that does not depend on
            // what the coverage beside it says. Written as a verdict, this fixture could claim a row
            // was at the point while handing in a coverage that says none is.
            items.put(role, new ItemAssessment.Owed(border.demand(role).criterion(),
                    coverage.apply(role), ItemAssessment.WritabilityProjection.PROVEN,
                    null));
        }
        return new BorderAssessment(border, items);
    }

    /** A row is at every point the border owes. */
    static Measurement<ItemAssessment.Coverage> hit(PointRole role) {
        return settled(new ItemAssessment.Coverage.Hit());
    }

    /**
     * One behavior's measures, as a verdict reads them.
     *
     * <p>The measures' own answers and not the entries beside them. What a reading was short of is
     * settled where the reading is, and reaches a verdict as the measure saying it was not made in
     * full — so a fixture here says which answer it is putting in front of the verdict, and the
     * step that decides that answer is tested where it happens
     * (souther-compiler, {@code AMeasureIsShortOfWhateverItsReadingDidNotReachTest}).
     */
    static PartitionEvidence partition(Measurement<List<BorderAssessment>> border) {
        return new PartitionEvidence(
                new Measurement.FailedToMeasure<>(
                        PartitionDerivation.TheReadingDidNotRunOut.THE_READING_DID_NOT_RUN_OUT,
                        WeakeningSet.of(new Weakening.ModelReadingIncomplete(
                                new souther.compiler.partition.ClosureGap.RulesNotReached(
                                        new souther.compiler.partition.AxisId("b", "t"))))),
                border,
                PartitionEvidence.PairSpace.NONE,
                List.of(), List.of(), List.of(), List.of(), List.of(),
                List.of());
    }

    /** The border measure made in full, over the one border. */
    static Measurement<List<BorderAssessment>> measured(BorderAssessment boundary) {
        return new Measurement.Complete<>(List.of(boundary));
    }

    /** And the same border, from a reading that was short of something — which is what a position
     *  the walk never reached the rules of leaves behind. */
    static Measurement<List<BorderAssessment>> shortOfSomething(BorderAssessment boundary) {
        return new Measurement.Partial<>(List.of(boundary),
                WeakeningSet.of(new Weakening.ModelReadingIncomplete(
                        new souther.compiler.partition.ClosureGap.RulesNotReached(
                                new souther.compiler.partition.AxisId("b", "m")))));
    }

    /** What one behavior's partition makes of the whole report, held to {@code held}. */
    static AdequacyReport.AdequacyStatus verdictOf(PartitionEvidence partition,
                                                   Adequacy.AdequacyBar held) {
        AdequacyReport.BehaviorReport behavior = new AdequacyReport.BehaviorReport(
                "weigh", souther.compiler.check.BehaviorImplementation.IMPLEMENTED,
                new souther.compiler.query.BehaviorEvidence(
                        Adequacy.RowReading.NONE, null, partition, null),
                souther.compiler.query.ClaimAnnotations.NONE, List.of());
        return new AdequacyReport(AdequacyReport.SCHEMA_VERSION, "test",
                held, WeakeningSet.none(),
                List.of(new AdequacyReport.ModuleReport("example.wide",
                        new SourceId("wide.sou"), List.of(behavior), List.of(), List.of())))
                .adequacy();
    }
}
