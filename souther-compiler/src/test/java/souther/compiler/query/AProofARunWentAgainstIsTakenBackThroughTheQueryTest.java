package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.check.PathReachability;
import souther.compiler.coverage.ArmReportAnchor;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.coverage.NumberingIdentity;
import souther.compiler.coverage.Numberings;
import souther.compiler.coverage.Observation;
import souther.compiler.coverage.RecordedConditionOutcome;
import souther.compiler.coverage.RunRecord;
import souther.compiler.coverage.SiteNumbering;
import souther.compiler.coverage.WalkProbe;
import souther.compiler.diag.SourcePos;
import souther.compiler.meta.ModulePath;
import souther.compiler.observe.ArmObservation;
import souther.compiler.observe.Counting;
import souther.compiler.observe.Run;
import souther.compiler.observe.RowOutcome;
import souther.compiler.query.Adequacy.RowReading;
import souther.compiler.reach.ComparisonArrival;
import souther.compiler.reach.PathDecision;
import souther.compiler.reach.Proof;
import souther.compiler.reach.Reachability;
import souther.compiler.reach.Witness;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A run recorded at a place a proof says nothing reaches takes that proof back where the runs of a
 * module are handed to the reading — for each kind of proof there is, and with the contradiction
 * written down.
 *
 * <p>No model has a row a proof is wrong about, so the runs here are recorded at the places the
 * numbering issued, which is what a row the proof was wrong about would be recorded doing. They go
 * through {@link Adequacy.Arrived#readAsRun}, where the runs become what the reading is handed,
 * and not through {@code asRunWith} with sets chosen here: the corrections themselves are held
 * where {@code asRunWith} is tested, and what is held here is that a kind of run reaches them.
 */
class AProofARunWentAgainstIsTakenBackThroughTheQueryTest {

    private static final String BEHAVIOR = "f";

    private static final SiteNumbering NUMBERING = Numberings.of(Numberings.Family.ARM,
            Numberings.Family.COMPARISON, Numberings.Family.COMPARISON, Numberings.Family.WALK);

    private static final NumberingIdentity IDENTITY = NUMBERING.identity();

    private static final SourceConstructOrigin FORK = origin(0, SourceConstruct.IF);
    private static final SourceConstructOrigin CONDITION = origin(1, SourceConstruct.IF);
    private static final SourceConstructOrigin APPLICATION = origin(2, SourceConstruct.CALL);
    private static final SourceConstructOrigin FOLD = origin(3, SourceConstruct.CALL);

    private static final ControlPlace.Arm ARM = new ControlPlace.Arm(Numberings.arm(FORK, 0),
            Optional.of(NUMBERING.arm(0)), new ArmReportAnchor.WhereItIsWritten(FORK));

    private static final ControlPlace.Outcome WAY = new ControlPlace.Outcome(
            ConstructOccurrence.asWritten(CONDITION), NUMBERING.outcome(1), true);

    private static final ConstructOccurrence ARRIVED_AT = ConstructOccurrence.asWritten(APPLICATION);

    private static final WalkProbe WALK = NUMBERING.walk(3);

    private static SourceConstructOrigin origin(int at, SourceConstruct construct) {
        return SourceConstructOrigin.written(new WrittenOwner.Body("fixture", "f"), at, construct);
    }

    private static Reachability shut() {
        return new Reachability.Unreachable(Proof.conditionsThatCannotAllHold(
                List.of(PathDecision.ofACondition(new SourcePos(1, 1), true))));
    }

    /** One of each proof, every one of them wrong if a run is where it says no run is. */
    private static PathReachability.Answers proven() {
        Optional<NumberingIdentity> numbering = Optional.of(IDENTITY);
        return new PathReachability.Answers(numbering, Map.of(ARM, shut(), WAY, shut()),
                new PathReachability.Arrivals(numbering,
                        Map.of(ARRIVED_AT, new ComparisonArrival.NothingArrives()),
                        Map.of(ARRIVED_AT, NUMBERING.outcome(2)), Map.of(),
                        Map.of(WALK, FOLD)));
    }

    /** A module with one row, which is only where a row to record a run on is had from. */
    private static final String A_ROW = """
            module demo

            data Amount = Int
                invariant value >= 0

            data Draft = { cost: Amount }
            data Submitted = { cost: Amount }
            data Rejected = { reason: String }

            behavior submit : (request: Draft) -> Submitted | Rejected
                constructs Submitted, Rejected

            let submit (request) = {
                guard request.cost.value <= 100 else Rejected { reason = "over" }
                Submitted { cost = request.cost }
            }

            example submit
                | "a small one" : (Draft { cost = Amount(50) }) -> Submitted { cost = Amount(50) }
            """;

    private static RowOutcome aRow() {
        Compilation compilation = Compilation.ofSources(List.of(A_ROW), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().getFirst();
        return compilation.exampleSourcesOf(module).stream()
                .flatMap(id -> compilation.db()
                        .ask(Output.Examples.asked(compilation.db(), module, id))
                        .value().rows().stream())
                .findFirst().orElseThrow(() -> new AssertionError("a row of the module"));
    }

    private static final RowOutcome ROW = aRow();

    /** The row, recorded as having gone {@code recorded} says, which is all that is changed. */
    private static RowOutcome recordedAs(RunRecord recorded) {
        return new RowOutcome(ROW.at(), ROW.target(), ROW.identity(), ROW.expectation(),
                ROW.stage(), ROW.disposition(), ROW.failurePhase(), ROW.expectedArm(),
                ROW.resultArm(), ROW.answer(), ROW.inputCases(), ROW.inputs(), ROW.statement(),
                new Run(ROW.run().applied(), new Counting.Read(0L, recorded)), ROW.replaced());
    }

    /** What reading a behavior's rows comes to when {@code rows} are the ones it saw. */
    private static RowReading seeing(RowOutcome... rows) {
        return new RowReading(new Measurement.Complete<>(new Adequacy.Observed(List.of(rows))),
                ArmObservation.RECORD);
    }

    /** A row recorded as {@code arms}, {@code ways} and {@code walksOn} say, of the module's
     *  numbering. */
    private static RowReading run(Set<Integer> arms, Set<RecordedConditionOutcome> ways,
                                  boolean walkedOn) {
        return seeing(recordedAs(new RunRecord.Recorded(new Observation(IDENTITY, arms, ways,
                Set.of(), Set.of(3), walkedOn ? Set.of(3) : Set.of()))));
    }

    private static PathReachability.Answers.AsRun readWith(RowReading... readings) {
        return readWith(Optional.of(NUMBERING), readings);
    }

    private static PathReachability.Answers.AsRun readWith(Optional<SiteNumbering> numbering,
                                                           RowReading... readings) {
        return Adequacy.Arrived.readAsRun(Map.of(BEHAVIOR, proven()), List.of(readings),
                numbering).get(BEHAVIOR);
    }

    @Test
    void runsThatWentAgainstNothingTakeNothingBack() {
        PathReachability.Answers.AsRun none = readWith();
        PathReachability.Answers.AsRun elsewhere = readWith(
                run(Set.of(), Set.of(new RecordedConditionOutcome(1, false)), false));

        assertEquals(PathReachability.Answers.Contradictions.NONE, none.contradicted(),
                "no run, so no proof is gone against");
        assertEquals(PathReachability.Answers.Contradictions.NONE, elsewhere.contradicted(),
                "and a run that entered the walk and took no second element, and saw the"
                        + " condition come out the way it was not proven never to, goes against"
                        + " none");
        assertInstanceOf(Reachability.Unreachable.class, elsewhere.answers().at(ARM));
        assertInstanceOf(Reachability.Unreachable.class, elsewhere.answers().at(WAY));
    }

    /** A row nothing watched, or one read under no numbering, is no run: it went nowhere that
     *  can be said, and so against no proof. */
    @Test
    void aRowNothingWatchedGoesAgainstNothing() {
        RowReading unwatched = seeing(recordedAs(new RunRecord.NoAccount()),
                recordedAs(new RunRecord.NoAccount()));
        RowReading unnumbered = run(Set.of(0), Set.of(), true);

        assertEquals(PathReachability.Answers.Contradictions.NONE,
                readWith(unwatched).contradicted());
        assertEquals(PathReachability.Answers.Contradictions.NONE,
                readWith(Optional.empty(), unnumbered).contradicted());
    }

    /**
     * The query is the reading of the module's own rows put through the method above: an arm a
     * row of the compiled module went through is the one a run is the witness of, and one no row
     * went through is not.
     */
    @Test
    void theQueryTakesInTheRowsOfTheModule() {
        Compilation compilation = Compilation.ofSources(List.of(A_ROW), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().getFirst();

        PathReachability.Answers answers = compilation.db().ask(new Adequacy.Arrived(module))
                .value().get("submit").answers();
        List<ControlPlace.Arm> witnessedByARun = answers.found().keySet().stream()
                .filter(ControlPlace.Arm.class::isInstance).map(ControlPlace.Arm.class::cast)
                .filter(arm -> arm.probe().isPresent()
                        && answers.at(arm).equals(new Reachability.Reachable(
                                Witness.aRunWentThrough(arm.probe().get()))))
                .toList();

        assertTrue(!witnessedByARun.isEmpty(), "the row went through an arm of the behavior");
        assertTrue(witnessedByARun.size() < answers.found().keySet().stream()
                        .filter(ControlPlace.Arm.class::isInstance).count(),
                "and not through the arm answering the request over the limit");
        assertTrue(compilation.db().dependenciesOf(new Adequacy.Arrived(module))
                        .contains(new Adequacy.RowReadings(module)),
                "and it is asked of the reading of the rows, so it is read again when that changes");
    }

    @Test
    void aRunThroughAnArmProvenShutTakesTheProofBack() {
        PathReachability.Answers.AsRun ran = readWith(run(Set.of(0), Set.of(), false));

        assertEquals(Set.of(ARM), ran.contradicted().places());
        assertInstanceOf(Reachability.Reachable.class, ran.answers().at(ARM));
        assertInstanceOf(Reachability.Unreachable.class, ran.answers().at(WAY),
                "and no other proof with it");
    }

    @Test
    void aRunBringingAConditionOutAWayProvenNeverToTakesTheProofBack() {
        PathReachability.Answers.AsRun ran = readWith(
                run(Set.of(), Set.of(new RecordedConditionOutcome(1, true)), false));

        assertEquals(Set.of(WAY), ran.contradicted().places());
        assertInstanceOf(Reachability.Reachable.class, ran.answers().at(WAY));
        assertInstanceOf(Reachability.Unreachable.class, ran.answers().at(ARM),
                "and no other proof with it");
    }

    @Test
    void aRunComingToAConstructProvenArrivedAtByNothingTakesTheProofBack() {
        PathReachability.Answers.AsRun ran = readWith(
                run(Set.of(), Set.of(new RecordedConditionOutcome(2, false)), false));

        assertEquals(Set.of(ARRIVED_AT), ran.contradicted().emptyArrivals());
        assertInstanceOf(ComparisonArrival.NoProjection.class,
                ran.answers().arrivals().arrivalAt(ARRIVED_AT));
    }

    @Test
    void aRunTakingASecondElementOfAWalkProvenToHaveOneAtMostTakesTheProofBack() {
        PathReachability.Answers.AsRun ran = readWith(run(Set.of(), Set.of(), true));

        assertEquals(Set.of(FOLD), ran.contradicted().walks());
        assertEquals(Set.of(), ran.answers().arrivals().walksHeldToOneAtMost().keySet());
    }

    @Test
    void whichRunWentAgainstAProofIsNoPartOfIt() {
        PathReachability.Answers.AsRun ran = readWith(
                run(Set.of(), Set.of(), false),
                run(Set.of(0), Set.of(), false),
                run(Set.of(), Set.of(new RecordedConditionOutcome(1, true)), true));

        assertEquals(Set.of(ARM, WAY), ran.contradicted().places(),
                "a proof is gone against by any one of the runs");
        assertEquals(Set.of(FOLD), ran.contradicted().walks());
    }
}
