package souther.cli;

import souther.compiler.source.SourceId;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.partition.BoundaryObligation;
import souther.compiler.partition.BoundaryTarget;
import souther.compiler.partition.Partitions;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.partition.AxisId;
import souther.compiler.partition.OriginRef;
import souther.compiler.query.BoundaryAssessment;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.TypeSymbol;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What {@code souther examples --strict} refuses.
 *
 * <p>It used to refuse a row waiting for a {@code let}, which is the one thing the specification says
 * is not a defect: an injected behavior's recorded row is the record of what that behavior owes, and a
 * model being migrated onto starts with nothing else. So the flag failed on the practice the
 * specification recommends and passed on the gap the same report had just printed.
 *
 * <p>These hold the flag to the other question. What it refuses is a gap an asked measure came to an
 * answer about, and how many rows are waiting has no bearing on it in either direction.
 */
class WhatStrictRefusesIsWhatTheRowsDoNotCoverTest {

    /** An injected behavior with a row recorded against it, and nothing a measure can fault. The
     *  boundary its invariant draws is the one thing to reach, and a row is on it. */
    private static final String ONLY_WAITING = """
            module example.rate

            data RiskScore = Int
                invariant value >= 0

            data Amount = Int
                invariant value >= 0

            behavior baseRate : (score: RiskScore) -> Amount

            example baseRate
                | "mid"      : (RiskScore(50)) -> Amount(10)
                | "score = 0" : (RiskScore(0)) -> Amount(0)
            """;

    /** The same model with the boundary row taken away: one gap, and the rows that remain are still
     *  waiting for the same {@code let}. */
    private static final String WAITING_AND_UNCOVERED = """
            module example.rate

            data RiskScore = Int
                invariant value >= 0

            data Amount = Int
                invariant value >= 0

            behavior baseRate : (score: RiskScore) -> Amount

            example baseRate
                | "mid" : (RiskScore(50)) -> Amount(10)
            """;

    /** A behavior with a body, an arm no row goes through, and no row waiting for anything. */
    private static final String UNCOVERED_ONLY = """
            module example.rate

            data Amount = Int
                invariant value >= 0

            data Charged = { cost: Amount }
            data Refused = { reason: String }

            behavior submit : (cost: Amount) -> Charged | Refused
                constructs Charged, Refused

            let submit (cost) = {
                guard cost.value <= 100 else Refused { reason = "over" }
                Charged { cost = cost }
            }

            example submit
                | "within" : (Amount(50)) -> Charged
            """;

    @Test
    void aRowWaitingForALetIsNotWhatStrictRefuses() throws Exception {
        Run run = examples(ONLY_WAITING, "--strict");

        assertEquals(0, run.code(), run.out() + run.err());
        assertTrue(run.out().contains("2 rows waiting for a `let`."), run.out());
        assertTrue(run.out().contains("adequacy: satisfied"), run.out());
    }

    @Test
    void aGapTheReportPrintsIsWhatStrictRefuses() throws Exception {
        Run run = examples(UNCOVERED_ONLY, "--strict");

        assertEquals(1, run.code(), run.out() + run.err());
        assertTrue(run.out().contains("0 rows waiting for a `let`."), run.out());
        assertTrue(run.out().contains("adequacy: not satisfied"), run.out());
        assertTrue(run.err().contains("the rows do not cover the model"), run.err());
    }

    /**
     * The round trip the report used to lose.
     *
     * <p>{@code --generate --boundaries} proposes a row for the boundary nothing sits on. Answering it
     * and pasting it back is what the generated block says to do, and it raises the number of rows
     * waiting for a {@code let} by one — which is the number the flag used to fail on. What it does to
     * the question the flag is named for is the opposite: the gap is gone.
     */
    @Test
    void generatedBoundaryRowCanImproveStrictAdequacyEvenWhilePendingRowsIncrease() throws Exception {
        Run before = examples(WAITING_AND_UNCOVERED, "--generate", "--boundaries", "--strict");

        assertEquals(1, before.code(), before.out() + before.err());
        assertTrue(before.out().contains("no row is at baseRate/score = 0"), before.out());
        assertTrue(before.out().contains("1 row waiting for a `let`."), before.out());
        // The row the block proposes, which is what the pasted model below answers.
        assertTrue(before.out().contains("| (RiskScore(0)) -> <?>"), before.out());

        Run after = examples(ONLY_WAITING, "--strict");

        assertEquals(0, after.code(), after.out() + after.err());
        assertTrue(after.out().contains("2 rows waiting for a `let`."), after.out());
        assertFalse(after.out().contains("no row is at"), after.out());
    }

    /**
     * The two gates answer the same question about the same model.
     *
     * <p>Held on a model whose only warnings are the adequacy ones, because {@code --warnings error}
     * refuses a build that warns at all. Where they disagree, one of them is reading the evidence a
     * second time.
     */
    @Test
    void strictAndAWarningsErrorBuildAgreeWhereNothingElseWarns() throws Exception {
        for (String model : List.of(ONLY_WAITING, WAITING_AND_UNCOVERED, UNCOVERED_ONLY)) {
            Path file = sourceOf(model);
            Path out = Files.createTempDirectory("souther-strict-out");

            Run examples = cli("examples", file.toString(), "--strict");
            Run compile = cli("compile", file.toString(), "-d", out.toString(),
                    "--adequacy", "all", "--warnings", "error");

            assertEquals(examples.code() != 0, compile.code() != 0,
                    model + "\n--- examples ---\n" + examples.err()
                            + "\n--- compile ---\n" + compile.err());
        }
    }

    /**
     * Every kind a build may refuse has something to refuse it under.
     *
     * <p>Whether a finding fails a build is a property of the kind and not of whether it carries a
     * code, and the two are written out separately so that neither is read off the other. A required
     * kind nobody gave a code to would be a gap a report prints and a build is never told about.
     */
    @Test
    void everyKindABuildMayRefuseHasADiagnosticCode() {
        for (Adequacy.Kind kind : Adequacy.Kind.values()) {
            if (kind.isAdequacyGap()) {
                assertTrue(kind.code().isPresent(), kind.name());
            }
        }
    }

    /**
     * An arm nothing reaches is a gap only where the arms were asked about.
     *
     * <p>The same model and the same rows; what differs is the level. At {@code witness} the arms are
     * not measured and the unreached one is not among the gaps, at {@code all} it is. What was asked
     * for is not readable from the evidence — a measure nobody wanted leaves the same absence as one
     * that could not be made — so the report carries it.
     */
    @Test
    void anArmIsAGapOnlyWhereTheArmsWereAskedAbout() {
        AdequacyReport armsNotAsked = reportOf(UNCOVERED_ONLY, Adequacy.Level.WITNESS);
        AdequacyReport armsAsked = reportOf(UNCOVERED_ONLY, Adequacy.Level.ALL);

        assertEquals(Adequacy.Level.WITNESS, armsNotAsked.askedLevel());
        assertTrue(armsNotAsked.adequacyGaps().stream()
                        .noneMatch(f -> f.kind() == Adequacy.Kind.ARM_UNREACHED),
                armsNotAsked.human(SourceNameResolver.identity()));
        assertTrue(armsAsked.adequacyGaps().stream()
                        .anyMatch(f -> f.kind() == Adequacy.Kind.ARM_UNREACHED),
                armsAsked.human(SourceNameResolver.identity()));
    }

    /**
     * A measure that does not apply is not a measure that failed.
     *
     * <p>A {@code >->} composition is implemented and has no arms of its own — its stages have them.
     * Its branch evidence is unavailable for that reason and not because anything went wrong, and a
     * verdict that read the evidence back would put every model holding a composition permanently out
     * of reach of {@code satisfied}.
     */
    @Test
    void aCompositionHasNoArmsOfItsOwnAndDoesNotHoldTheVerdictOpen() {
        AdequacyReport report = reportOf(COMPOSED, Adequacy.Level.ALL);

        String human = report.human(SourceNameResolver.identity());
        assertEquals(AdequacyReport.AdequacyStatus.SATISFIED, report.adequacy(), human);
        assertFalse(human.contains("the arms were not measured"), human);
    }

    /**
     * What a dropped axis cost decides whether the verdict stays open.
     *
     * <p>Neither kind leaves a boundary behind, which is also what a position the rows cover looks
     * like. An axis that was carrying a line some rule drew took boundaries nothing can ask about now,
     * so the rows there are unmeasured rather than adequate. An axis that was only classifying took a
     * measure no build refuses over, and holding the verdict open for it would report a doubt nobody
     * can act on.
     *
     * <p>Written from the evidence rather than from a source: reaching the limit takes thirteen axes
     * on one behavior, and a fixture that size says less than this does about which of the two it is.
     */
    @Test
    void anAxisDroppedPastTheLimitHoldsTheVerdictOpenOnlyWhereItCarriedAnObligation() {
        BoundaryAssessment met = new BoundaryAssessment(
                new BoundaryObligation(
                        new BoundaryTarget.AtPlace(new AxisId("weigh", "w.a"), Carrier.WHOLE,
                                Count.of(100)),
                        new OriginRef.InvariantOrigin(
                                TypeSymbols.declared(new TypeKey("example.rate", "Amount")), "value <= 100"),
                        BoundaryObligation.BoundarySide.AT),
                new BoundaryAssessment.Coverage.Hit(),
                new BoundaryAssessment.Writability.WitnessedByRow(),
                new BoundaryAssessment.Attempt.NotAttempted(
                        BoundaryAssessment.Attempt.Reason.A_ROW_IS_ALREADY_THERE));

        assertEquals(AdequacyReport.AdequacyStatus.SATISFIED, verdictOf(partition(met)),
                "nothing dropped");
        assertEquals(AdequacyReport.AdequacyStatus.SATISFIED,
                verdictOf(partition(met, dropped("weigh", "w.flag", false))),
                "a dropped axis that was only classifying");
        assertEquals(AdequacyReport.AdequacyStatus.UNDETERMINED,
                verdictOf(partition(met, dropped("weigh", "w.m", true))),
                "a dropped axis that was carrying a boundary");
    }

    private static Partitions.OmittedAxis dropped(String behavior, String path,
                                                  boolean carriedAnObligation) {
        return new Partitions.OmittedAxis(new AxisId(behavior, path), carriedAnObligation);
    }

    private static PartitionEvidence partition(BoundaryAssessment boundary,
                                               Partitions.OmittedAxis... omitted) {
        return new PartitionEvidence(PartitionEvidence.Partitioned.of(List.of()),
                PartitionEvidence.Bounded.of(List.of(boundary)), PartitionEvidence.PairSpace.NONE,
                List.of(), List.of(), List.of(omitted), List.of(), List.of());
    }

    /** What one behavior's partition makes of the whole report, with nothing else asked about. */
    private static AdequacyReport.AdequacyStatus verdictOf(PartitionEvidence partition) {
        AdequacyReport.BehaviorReport behavior = new AdequacyReport.BehaviorReport(
                "weigh", false, 1, 0, MeasurementStatus.COMPLETE, null, partition,
                null, List.of());
        return new AdequacyReport(AdequacyReport.SCHEMA_VERSION, "test", Adequacy.Level.ALL,
                MeasurementStatus.COMPLETE,
                List.of(new AdequacyReport.ModuleReport("example.wide", new SourceId("wide.sou"), MeasurementStatus.COMPLETE,
                        List.of(), List.of(behavior))))
                .adequacy();
    }

    /** Two covered stages and the composition of them, which carries rows of its own. */
    private static final String COMPOSED = """
            module example.pipe

            data Amount = Int
                invariant value >= 0

            data Doubled = { of: Amount }
            data Tripled = { of: Amount }

            behavior twice : (cost: Amount) -> Doubled
                constructs Doubled

            let twice (cost) = Doubled { of = cost }

            behavior thrice : (d: Doubled) -> Tripled
                constructs Tripled

            let thrice (d) = Tripled { of = d.of }

            behavior both = twice >-> thrice

            example twice
                | "zero" : (Amount(0)) -> Doubled { of = Amount(0) }

            example thrice
                | "zero" : (Doubled { of = Amount(0) }) -> Tripled { of = Amount(0) }

            example both
                | "zero" : (Amount(0)) -> Tripled { of = Amount(0) }
            """;

    /**
     * A behavior with no rows is not a behavior with gaps.
     *
     * <p>Nothing was measured, so nothing was found, and calling that satisfied would let a model pass
     * by writing no rows at all. The verdict says undetermined and the flag lets it through, which is
     * what {@code --warnings error} does with the same model.
     */
    @Test
    void aModelNothingWasMeasuredOnIsUndetermined() throws Exception {
        String noRows = """
                module example.rate

                data RiskScore = Int
                    invariant value >= 0

                data Amount = Int
                    invariant value >= 0

                behavior baseRate : (score: RiskScore) -> Amount
                """;
        Run run = examples(noRows, "--strict");

        assertEquals(0, run.code(), run.out() + run.err());
        assertTrue(run.out().contains("adequacy: undetermined"), run.out());
        assertEquals(AdequacyReport.AdequacyStatus.UNDETERMINED,
                reportOf(noRows, Adequacy.Level.ALL).adequacy());
    }

    /**
     * A report of one behavior answers about that behavior.
     *
     * <p>The verdict is worked out from what the report holds every time it is asked, so filtering
     * cannot leave a verdict about behaviors the reader cannot see. What was asked for is carried
     * through untouched: filtering changes what is shown, not what was measured.
     */
    @Test
    void aFilteredReportAnswersAboutWhatItShows() {
        AdequacyReport whole = reportOf(BOTH, Adequacy.Level.ALL);
        AdequacyReport covered = whole.only(null, "baseRate");
        AdequacyReport uncovered = whole.only(null, "submit");

        assertEquals(AdequacyReport.AdequacyStatus.NOT_SATISFIED, whole.adequacy(),
                whole.human(SourceNameResolver.identity()));
        assertEquals(AdequacyReport.AdequacyStatus.SATISFIED, covered.adequacy(),
                covered.human(SourceNameResolver.identity()));
        assertEquals(AdequacyReport.AdequacyStatus.NOT_SATISFIED, uncovered.adequacy(),
                uncovered.human(SourceNameResolver.identity()));
        assertEquals(whole.askedLevel(), covered.askedLevel());
    }

    /** One module holding both of the models above, so that filtering has something to filter. */
    private static final String BOTH = """
            module example.rate

            data RiskScore = Int
                invariant value >= 0

            data Amount = Int
                invariant value >= 0

            data Charged = { cost: Amount }
            data Refused = { reason: String }

            behavior baseRate : (score: RiskScore) -> Amount

            behavior submit : (cost: Amount) -> Charged | Refused
                constructs Charged, Refused

            let submit (cost) = {
                guard cost.value <= 100 else Refused { reason = "over" }
                Charged { cost = cost }
            }

            example baseRate
                | "mid"       : (RiskScore(50)) -> Amount(10)
                | "score = 0" : (RiskScore(0)) -> Amount(0)

            example submit
                | "within" : (Amount(50)) -> Charged
            """;

    private static AdequacyReport reportOf(String source, Adequacy.Level level) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(level));
        compilation.answerEverything();
        return AdequacyReport.of(compilation);
    }

    private record Run(int code, String out, String err) {}

    private static Path sourceOf(String model) throws Exception {
        Path file = Files.createTempDirectory("souther-strict").resolve("rate.sou");
        Files.writeString(file, model);
        return file;
    }

    private static Run examples(String model, String... extraArgs) throws Exception {
        List<String> args = new ArrayList<>(List.of("examples", sourceOf(model).toString()));
        args.addAll(List.of(extraArgs));
        return cli(args.toArray(String[]::new));
    }

    private static Run cli(String... args) {
        PrintStream originalOut = System.out;
        PrintStream originalErr = System.err;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        System.setErr(new PrintStream(err, true, StandardCharsets.UTF_8));
        int code;
        try {
            code = Main.dispatch(args);
        } finally {
            System.setOut(originalOut);
            System.setErr(originalErr);
        }
        return new Run(code, out.toString(StandardCharsets.UTF_8),
                err.toString(StandardCharsets.UTF_8));
    }
}
