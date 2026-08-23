package souther.cli;


import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.partition.Partitions;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.partition.AxisId;
import souther.compiler.query.BorderAssessment;
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
     * The refusal points at the entries in the terms of the report the reader was given.
     *
     * <p>A count is worth something beside a way of finding what it counts, and the two surfaces name
     * the same findings differently: a person reads a mark and a consumer reads a field. Naming the
     * mark whatever was printed sent a reader of a JSON document looking for a character that is
     * nowhere in it.
     */
    @Test
    void theRefusalNamesTheFindingsTheWayTheReportItPrintedDoes() throws Exception {
        Run human = examples(UNCOVERED_ONLY, "--strict");
        Run json = examples(UNCOVERED_ONLY, "--strict", "--format", "json");

        assertEquals(1, json.code(), json.out() + json.err());
        assertTrue(human.err().contains("marked `!` above"), human.err());
        assertTrue(json.err().contains("`disposition: refused`"), json.err());
        assertFalse(json.err().contains("`!`"), json.err());
        // The word the document it just printed says it under.
        assertTrue(json.out().contains("\"disposition\" : \"refused\""), json.out());
        assertFalse(json.out().contains("!"), "a JSON document carries no mark: " + json.out());
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
        assertTrue(before.out().contains("no row is at the ON point baseRate/score = 0"), before.out());
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
     *
     * <p>Against the build held to the same bar. {@code souther examples} measures everything and is
     * held to reliable domain coverage, so the compile this is put beside is the one that asks for
     * that criterion; put beside {@code --adequacy all} the two answer to different bars, and
     * agreeing would be the accident of a model with no point away from a line left uncovered.
     */
    @Test
    void strictAndAWarningsErrorBuildAgreeWhereNothingElseWarns() throws Exception {
        for (String model : List.of(ONLY_WAITING, WAITING_AND_UNCOVERED, UNCOVERED_ONLY,
                ON_THE_LINE_ONLY)) {
            Path file = sourceOf(model);
            Path out = Files.createTempDirectory("souther-strict-out");

            Run examples = cli("examples", file.toString(), "--strict");
            Run compile = cli("compile", file.toString(), "-d", out.toString(),
                    "--adequacy", "reliable-domain", "--warnings", "error");

            assertEquals(examples.code() != 0, compile.code() != 0,
                    model + "\n--- examples ---\n" + examples.err()
                            + "\n--- compile ---\n" + compile.err());
        }
    }

    /**
     * A model covered against the lines and at neither point away from them.
     *
     * <p>The two criteria differ here and nowhere else in this class, which is what makes the
     * agreement above something rather than an accident: simplified domain coverage asks for the row
     * on the line and the row one step over, and this has both.
     */
    private static final String ON_THE_LINE_ONLY = """
            module example.limit

            data Ok
            data TooHigh

            behavior grade : (score: Int) -> Ok | TooHigh

            let grade (score) = {
                guard score <= 100 else TooHigh
                Ok
            }

            example grade
                | "on the line" : (100) -> Ok
                | "a step over" : (101) -> TooHigh
            """;

    /**
     * The command that reports and the build that refuses say the same thing about one model.
     *
     * <p>What this was. {@code souther examples} was measuring every point of every border and
     * being held to a build's default criterion, so it printed the two points away from the line and
     * then called the model satisfied — while {@code souther compile --adequacy reliable-domain
     * --warnings error} refused the same model over the same two points. A CI running both was told
     * the model was covered and that the build was refused.
     *
     * <p>The build held to the other criterion is here too, and it succeeds. Without it this passes
     * on a model where the two bars ask for the same thing, and every word about criteria in it would
     * be describing something the test never exercises.
     */
    @Test
    void strictRefusesThePointsAwayFromALineTheWayAReliableDomainBuildDoes() throws Exception {
        Path file = sourceOf(ON_THE_LINE_ONLY);

        Run examples = cli("examples", file.toString(), "--strict");
        Run reliable = cli("compile", file.toString(),
                "-d", Files.createTempDirectory("souther-reliable").toString(),
                "--adequacy", "reliable-domain", "--warnings", "error");
        Run simplified = cli("compile", file.toString(),
                "-d", Files.createTempDirectory("souther-simplified").toString(),
                "--adequacy", "all", "--warnings", "error");

        assertEquals(1, examples.code(), examples.out() + examples.err());
        assertTrue(examples.out().contains("adequacy: not satisfied"), examples.out());
        assertTrue(examples.out().contains("! no row is at an IN point"), examples.out());
        assertTrue(examples.out().contains("! no row is at an OUT point"), examples.out());
        assertEquals(1, reliable.code(), reliable.out() + reliable.err());
        assertTrue(reliable.err().contains("E1917"), reliable.err());
        assertEquals(0, simplified.code(),
                "the two criteria differ on this model: " + simplified.out() + simplified.err());
    }

    /**
     * {@code --strict} decides an exit status and says nothing about the model.
     *
     * <p>What a reader is shown is one report, whether or not the run was asked to fail on it. A flag
     * that moved the bar would answer one model two ways from one command, and a reader comparing a
     * strict run's output against an earlier one would read the difference as the rows having
     * changed.
     */
    @Test
    void theReportIsWhatItIsWhetherOrNotTheRunWasAskedToBeStrict() throws Exception {
        Path file = sourceOf(ON_THE_LINE_ONLY);

        Run lenient = cli("examples", file.toString());
        Run strict = cli("examples", file.toString(), "--strict");

        assertEquals(lenient.out(), strict.out());
        assertEquals(0, lenient.code(), lenient.err());
        assertEquals(1, strict.code(), strict.err());
    }

    /**
     * Every kind some criterion refuses over has something to refuse it under.
     *
     * <p>What a criterion asks for and what a kind carries are written out separately so that neither
     * is read off the other. A kind some build can be held to and nobody gave a code to would be a
     * gap a report prints and a build is never told about.
     */
    @Test
    void everyKindACriterionRefusesOverHasADiagnosticCode() {
        for (Adequacy.Criterion criterion : Adequacy.Criterion.values()) {
            for (Adequacy.Kind kind : Adequacy.Kind.values()) {
                if (criterion.refuses(kind)) {
                    assertTrue(kind.code().isPresent(), criterion + " refuses over " + kind);
                }
            }
        }
    }

    /**
     * And it is told as a warning, which is the other half of being able to refuse over it.
     *
     * <p>Whether a code is reported as an error or a warning is a set written by hand a package
     * away, and nothing tied it to this. A gap a build refuses over that is not among them is raised
     * as an error out of the measure that found it, which is not a compile error and is not the
     * warning `--warnings` decides about — the state E1917 was in until it was noticed by running
     * the command.
     */
    @Test
    void everyKindACriterionRefusesOverIsToldAsAWarning() {
        for (Adequacy.Criterion criterion : Adequacy.Criterion.values()) {
            for (Adequacy.Kind kind : Adequacy.Kind.values()) {
                if (!criterion.refuses(kind)) {
                    continue;
                }
                assertEquals(souther.compiler.diag.Severity.WARNING,
                        kind.code().orElseThrow().severity(),
                        criterion + " refuses over " + kind + ", so its code is one a build is"
                                + " warned about rather than one a compile fails on");
            }
        }
    }

    /**
     * The two criteria differ over the points away from a line and over nothing else.
     *
     * <p>Read off the criteria rather than listed, so a kind added and given to one of them and not
     * the other is this failing rather than a silent second difference between the bars.
     */
    @Test
    void theTwoCriteriaDifferOverThePointsAwayFromALine() {
        List<Adequacy.Kind> differing = new java.util.ArrayList<>();
        for (Adequacy.Kind kind : Adequacy.Kind.values()) {
            if (Adequacy.Criterion.SIMPLIFIED_DOMAIN.refuses(kind)
                    != Adequacy.Criterion.RELIABLE_DOMAIN.refuses(kind)) {
                differing.add(kind);
            }
        }
        assertEquals(List.of(Adequacy.Kind.DOMAIN_POINT_UNCOVERED), differing);
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
     * <p>What a verdict does with the answer, and not what a dropped axis does to the answer. The
     * second is settled where the reading is and reaches a verdict only as the measure's own status
     * — so this hands the verdict each status in turn, and that a dropped axis carrying a line
     * produces the second of them is held against a source in souther-compiler
     * ({@code AMeasureIsShortOfWhateverItsReadingDidNotReachTest}). Written the other way round,
     * this fixture would name a status of its own choosing and call the naming a test.
     */
    @Test
    void anAxisDroppedPastTheLimitHoldsTheVerdictOpenOnlyWhereItCarriedAnObligation() {
        BorderAssessment met = AReportOfOneBorder.assessed(
                AReportOfOneBorder.aBorderAtTheEdgeOfItsDomain(), AReportOfOneBorder::hit);

        assertEquals(AdequacyReport.AdequacyStatus.SATISFIED,
                verdictOf(partition(AReportOfOneBorder.measured(met))),
                "a border measure made in full");
        // The same border, from a reading that was short of something. Which is what a dropped axis
        // carrying a line leaves the measure with, and the verdict reads the measure's answer and
        // never the list of what was dropped: a report working out for itself what an omission cost
        // is a second reading of a question the measure has already answered.
        assertEquals(AdequacyReport.AdequacyStatus.UNDETERMINED,
                verdictOf(partition(AReportOfOneBorder.shortOfSomething(met),
                        dropped("weigh", "w.m", true))),
                "a border measure that was not made in full");
        assertEquals(AdequacyReport.AdequacyStatus.SATISFIED,
                verdictOf(partition(AReportOfOneBorder.measured(met),
                        dropped("weigh", "w.flag", false))),
                "a dropped axis the border measure was not measuring");
    }

    private static Partitions.OmittedAxis dropped(String behavior, String path,
                                                  boolean carriedAnObligation) {
        return new Partitions.OmittedAxis(new AxisId(behavior, path), carriedAnObligation);
    }

    /** This one asks nothing about the criterion, so it is held to the one a build asks for by
     *  default; {@link AReportOfOneBorder} is where the report itself is built. */
    private static PartitionEvidence partition(souther.compiler.query.Measurement<List<BorderAssessment>> border,
                                               Partitions.OmittedAxis... omitted) {
        return AReportOfOneBorder.partition(border, omitted);
    }

    private static AdequacyReport.AdequacyStatus verdictOf(PartitionEvidence partition) {
        return AReportOfOneBorder.verdictOf(partition, Adequacy.Criterion.SIMPLIFIED_DOMAIN);
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
                | "zero"     : (Amount(0)) -> Doubled { of = Amount(0) }
                | "positive" : (Amount(1)) -> Doubled { of = Amount(1) }

            example thrice
                | "zero"     : (Doubled { of = Amount(0) }) -> Tripled { of = Amount(0) }
                | "positive" : (Doubled { of = Amount(1) }) -> Tripled { of = Amount(1) }

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
