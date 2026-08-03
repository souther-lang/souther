package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Diagnostic;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Db;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What is said when some of what a row wrote could not be read.
 *
 * <p>The whole feature rests on three answers where two would fit: met, unmet, and *not decided*. The
 * measures each knew that, and the aggregate in front of them did not — it handed on the rows and
 * dropped the reasons the rest were missing, so every measure downstream read "what was observed" as
 * "what there was". These hold each of them to the third answer.
 */
class CompilePartialAdequacyTest {

    /** A row that never comes back: the helper loops, so its evaluation is stopped rather than
     * finished, and what it went through on the way goes with it. */
    private static final String TIMES_OUT = """
            module example.loop

            data Draft = { n: Int }
            data Done = { n: Int }
            data Small = { n: Int }

            partial let spin (n: Int): Int = spin(n)

            behavior go : (request: Draft) -> Done | Small
                constructs Done, Small

            let go (request) = {
                guard request.n <= 0 else Done { n = spin(request.n) }
                Small { n = request.n }
            }

            example go
                | (Draft { n = 1 }) -> Done { n = 1 }
            """;

    /**
     * An input whose observation is cut short before the position a rule is about.
     *
     * <p>The collection ahead of it spends the node budget, so `cost` is truncated — while the row
     * writes exactly the number the invariant's lower bound names.
     */
    private static String budgetSpent(String tail) {
        StringBuilder inner = new StringBuilder();
        for (int i = 0; i < 64; i++) {
            inner.append(i == 0 ? "" : ", ")
                    .append("Item { a = \"").append(i).append("\", b = \"").append(i)
                    .append("\", c = \"").append(i).append("\" }");
        }
        StringBuilder groups = new StringBuilder();
        for (int i = 0; i < 64; i++) {
            groups.append(i == 0 ? "" : ", ").append("Group { items = [ ").append(inner).append(" ] }");
        }
        return """
                module example.budget

                data Amount = Int
                    invariant value >= 0 && value <= 1000

                data Yes
                data No
                data Flag = Yes | No

                data Item = { a: String, b: String, c: String }
                data Group = { items: List<Item> }

                data Draft = { groups: List<Group>, cost: Amount, flag: Flag }
                data Ok = { n: Int }

                behavior take : (request: Draft) -> Ok
                    constructs Ok

                let take (request) = Ok { n = request.cost.value }

                example take
                    | (Draft { groups = [ %s ], cost = Amount(0), flag = Yes }) -> Ok { n = 0 }
                """.formatted(groups) + tail;
    }

    /** Compiles are shared between the cases that read the same model. A row here is one that never
     * comes back, so each of these costs the whole evaluation budget. */
    private static final Map<String, Compilation> COMPILED = new java.util.LinkedHashMap<>();

    private static Compilation measured(String source) {
        return COMPILED.computeIfAbsent("report:" + source, _ -> {
            Compilation compilation = Compilation.ofSource(source, "Main");
            compilation.measure(Adequacy.Asked.reportOnly());
            compilation.answerEverything();
            return compilation;
        });
    }

    private static Compilation warned(String source) {
        return COMPILED.computeIfAbsent("warn:" + source, _ -> {
            Compilation compilation = Compilation.ofSource(source, "Main");
            compilation.measure(Adequacy.Level.ALL);
            compilation.answerEverything();
            return compilation;
        });
    }

    private static List<String> warningCodes(Compilation compilation) {
        List<String> codes = new ArrayList<>();
        for (Db.Found found : compilation.db().allReports()) {
            Diagnostic d = found.report().diagnostic();
            if (!found.report().isError() && d.code() != null && d.code().startsWith("E19")) {
                codes.add(d.code());
            }
        }
        return codes;
    }

    /**
     * A row that did not finish went somewhere before it stopped.
     *
     * <p>What it went through was dropped with it, so the arms it did not light are undecided rather
     * than unreached — and every arm of the behavior would otherwise be reported as one no row goes
     * through, on the strength of a run nobody let finish.
     */
    @Test
    void aBranchMeasureOverAnUnfinishedRowIsUndecided() {
        Compilation compilation = measured(TIMES_OUT);
        Adequacy.BranchEvidence branch = compilation.db()
                .ask(new Adequacy.BranchCoverage(compilation.modules().get(0))).value().get("go");

        assertEquals(2, branch.all().size(), "the arms are there");
        assertEquals(MeasurementStatus.PARTIAL, branch.status());
        assertEquals(List.of(), branch.covered().stream().sorted().toList());
    }

    /** And nothing is warned about from it. */
    @Test
    void anUndecidedBranchMeasureWarnsAboutNoArm() {
        assertFalse(warningCodes(warned(TIMES_OUT)).contains("E1918"),
                "an arm a row might have gone through is not an arm nothing reaches");
    }

    /**
     * A value the observation could not reach is not a value that missed.
     *
     * <p>The row here writes the very number the invariant's lower bound names. Its observation was
     * cut short by a limit reached elsewhere in the same input, and reporting that as "no row is at
     * this boundary" states something about the model that is not true.
     */
    @Test
    void aBoundaryWhosePositionWasNotReadIsUndecided() {
        PartitionEvidence partition = measured(budgetSpent("")).db()
                .ask(new Adequacy.Coverage("example.budget")).value().get("take");

        List<PartitionEvidence.BoundaryCoverage> at = partition.boundaries().stream()
                .filter(b -> b.value().equals("0")).toList();
        assertEquals(1, at.size());
        assertEquals(MeasurementStatus.PARTIAL, at.get(0).status());
        assertFalse(at.get(0).hit(), "nothing was read, so nothing was met either");
    }

    @Test
    void anUndecidedBoundaryWarnsAboutNothing() {
        assertFalse(warningCodes(warned(budgetSpent(""))).contains("E1916"),
                "a boundary whose position was not read is not a boundary nothing is at");
    }

    /**
     * A class a row may already sit in is not a class to write a row for.
     *
     * <p>The worst of these to get wrong. A warning is a claim; a generated row is a specific piece of
     * work handed to a person, and handing them work that is already done is worse than saying nothing.
     */
    @Test
    void nothingIsGeneratedForAPositionThatCouldNotBeRead() {
        Compilation compilation = measured(budgetSpent(""));
        Map<String, Adequacy.Filling> generated = compilation.db()
                .ask(new Adequacy.Generated("example.budget")).value();
        assertNotNull(generated);

        assertEquals(List.of(), generated.get("take").pairs().rows(),
                "the flag's classes are undecided, so nothing is written for them");
        assertFalse(generated.get("take").pairs().incompleteness().isEmpty(),
                "and the position that could not be read is named");
        assertEquals("", GeneratedRows.of("example.budget", generated, true));
    }

    /**
     * The rows the compile ran are what every measure reads, reasons included.
     *
     * <p>The evaluation keeps observations and the reasons for their absence apart on purpose. An
     * aggregate that passed on the first and dropped the second would answer as if the reason were
     * nothing, which is the one reading the whole design is against.
     */
    @Test
    void whatStoppedARowBeingSeenReachesTheMeasureThatReadsIt() {
        Compilation compilation = measured(TIMES_OUT);
        Adequacy.SignatureEvidence signature = compilation.db()
                .ask(new Adequacy.Witnesses(compilation.modules().get(0))).value().get("go");

        assertEquals(MeasurementStatus.PARTIAL, signature.status());
        assertFalse(warningCodes(warned(TIMES_OUT)).contains("E1913"),
                "a case the unfinished row might have produced is not a case nothing claims");
    }

    /**
     * A report about one behavior says nothing about another.
     *
     * <p>`--behavior submit` is a promise about what the output is about. A status of `partial` whose
     * reason names a behavior the report does not show is a status nothing in front of the reader
     * accounts for.
     */
    @Test
    void filteringToOneBehaviorLeavesAnotherBehaviorsReasonsBehind() {
        Compilation compilation = measured("""
                module example.two

                data Draft = { n: Int }
                data Ok = { n: Int }
                data Gone = { why: String }

                partial let spin (n: Int): Int = spin(n)

                behavior submit : (request: Draft) -> Ok
                    constructs Ok

                let submit (request) = Ok { n = request.n }

                behavior cancel : (request: Draft) -> Gone
                    constructs Gone

                let cancel (request) = Gone { why = "x" }

                example submit
                    | (Draft { n = 1 }) -> Ok { n = 1 }

                example cancel
                    | (Draft { n = spin(1) }) -> Gone { why = "x" }
                """);
        AdequacyReport whole = AdequacyReport.of(compilation);

        assertEquals(MeasurementStatus.PARTIAL, whole.status(), "`cancel` did not finish");
        assertEquals(List.of("cancel"), whole.modules().get(0).incompleteness().stream()
                .map(souther.compiler.observe.Incompleteness::subject).toList());

        AdequacyReport one = whole.only(null, "submit");
        assertEquals(MeasurementStatus.COMPLETE, one.status());
        assertEquals(List.of(), one.modules().get(0).incompleteness());
        assertTrue(one.modules().get(0).behaviors().stream()
                .allMatch(b -> b.name().equals("submit")));
    }

    /** The row that did not finish is still there to be counted, and still says it did not. */
    @Test
    void theUnfinishedRowIsStillReported() {
        Compilation compilation = measured(TIMES_OUT);
        String sourceId = compilation.exampleSourcesOf("example.loop").get(0);

        List<souther.compiler.observe.RowOutcome> rows = compilation.db()
                .ask(new Adequacy.ProbedExamples("example.loop", sourceId)).value().rows();

        assertEquals(1, rows.size());
        assertEquals(Disposition.INCOMPLETE, rows.get(0).disposition());
    }
}
