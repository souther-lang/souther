package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.MeasurementStatus;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which arms of a body the rows go through.
 *
 * <p>Branch-<em>arm</em> coverage, which is a lower bound on covering what a body can do and not the
 * same thing. Nothing here reports it as paths covered: going through both arms of two nested
 * conditions is four arms and says nothing about whether their combinations were tried.
 */
class CompileExampleCoverageTest {

    private static final String MODEL = """
            module example.trip

            data Amount = Int
                invariant value >= 0

            data Draft = { cost: Amount }
            data Submitted = { cost: Amount }
            data Waiting = { cost: Amount }

            behavior submit : (request: Draft) -> Submitted | Waiting
                constructs Submitted, Waiting

            let submit (request) = {
                guard request.cost.value <= 100 else Waiting { cost = request.cost }
                Submitted { cost = request.cost }
            }
            """;

    private static Adequacy.BranchEvidence branch(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        // Measuring the arms is opted into, so a test about them opts in.
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        Map<String, Adequacy.BranchEvidence> all = compilation.db()
                .ask(new Adequacy.BranchCoverage(compilation.modules().get(0))).value();
        assertNotNull(all, "the model under test compiles");
        return all.get(behavior);
    }

    private static List<String> unreached(Adequacy.BranchEvidence branch) {
        return branch.unreached().stream()
                .map(souther.compiler.coverage.CoverageSites.Site::label).toList();
    }

    /** One row through the guard leaves the other arm with nothing going through it. */
    @Test
    void anArmNoRowGoesThroughIsNamed() {
        Adequacy.BranchEvidence branch = branch(MODEL + """

                example submit
                    | (Draft { cost = Amount(50) }) -> Submitted { cost = Amount(50) }
                """, "submit");

        assertEquals(MeasurementStatus.COMPLETE, branch.status());
        assertEquals(2, branch.all().size(), "a guard is two arms");
        assertEquals(List.of("else"), unreached(branch));
    }

    @Test
    void aRowThroughEachArmLeavesNothingUnreached() {
        Adequacy.BranchEvidence branch = branch(MODEL + """

                example submit
                    | (Draft { cost = Amount(50) })  -> Submitted { cost = Amount(50) }
                    | (Draft { cost = Amount(500) }) -> Waiting { cost = Amount(500) }
                """, "submit");

        assertEquals(List.of(), unreached(branch));
        assertEquals(2, branch.covered().size());
    }

    /** A match's arms are counted one per arm, and cases written together on one arm are one. */
    @Test
    void aMatchIsOneArmPerArmAndNotPerCase() {
        Adequacy.BranchEvidence branch = branch("""
                module example.trip

                data Domestic
                data Overseas
                data Local
                data Kind = Domestic | Overseas | Local

                data Fee = { amount: Int }

                behavior feeFor : (kind: Kind) -> Fee
                    constructs Fee

                let feeFor (kind) = match kind with
                    | Domestic | Local -> Fee { amount = 0 }
                    | Overseas -> Fee { amount = 100 }

                example feeFor
                    | (Domestic) -> Fee { amount = 0 }
                """, "feeFor");

        assertEquals(2, branch.all().size(), "two arms, though there are three cases");
        assertEquals(List.of("case Overseas"), unreached(branch));
    }

    /**
     * A row that did not finish contributes nothing.
     *
     * <p>What a row reached before it ran out of time is some of what it would have reached, and
     * counting it would report arms as covered on the strength of a run nobody let finish. The row is
     * recorded as undecided instead.
     */
    @Test
    void aRowThatRanOutOfTimeCountsForNothing() {
        String spinning = """
                module example.loop

                data Draft = { n: Int }
                data Done = { n: Int }

                partial let spin (n: Int): Int = spin(n)

                behavior go : (request: Draft) -> Done
                    constructs Done

                let go (request) = {
                    guard request.n <= 0 else Done { n = spin(request.n) }
                    Done { n = request.n }
                }

                example go
                    | (Draft { n = 1 }) -> Done { n = 1 }
                """;
        Compilation compilation = Compilation.ofSource(spinning, "Main")
                .withDeadline(DoesNotComeBack.overrunningOn("row 1 of `go`"));
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        String sourceId = compilation.exampleSourcesOf(module).get(0);
        List<souther.compiler.observe.RowOutcome> rows = compilation.db()
                .ask(new Adequacy.ProbedExamples(module, sourceId)).value().rows();

        assertEquals(1, rows.size());
        assertEquals(souther.compiler.observe.Disposition.INCOMPLETE, rows.get(0).disposition(),
                "the row is the one that never came back");
        assertEquals(souther.compiler.observe.FailurePhase.TIMEOUT, rows.get(0).failurePhase());
        assertEquals(java.util.Set.of(), rows.get(0).hits(),
                "and what it went through on the way is not read");

        Adequacy.BranchEvidence branch = compilation.db()
                .ask(new Adequacy.BranchCoverage(module)).value().get("go");
        assertEquals(2, branch.all().size(), "the arms are there to reach");
        assertEquals(List.of(), branch.covered().stream().sorted().toList(),
                "a row that never came back left no arms behind");
    }

    // --- what opts a behavior into being measured -------------------------------------------------

    /**
     * Reaching a behavior sideways does not ask it about its arms.
     *
     * <p>The measurement is opted into by writing a row. A behavior somebody else's row happens to run
     * through has had no claim made about it, and telling its author about arms nothing reaches would be
     * answering a question they did not ask.
     */
    @Test
    void aBehaviorReachedOnlyThroughAnotherIsNotAskedAboutItsArms() {
        String indirect = """
                module example.trip

                data Amount = Int
                    invariant value >= 0

                data Draft = { cost: Amount }
                data Submitted = { cost: Amount }
                data Waiting = { cost: Amount }

                behavior classify : (cost: Amount) -> Submitted | Waiting
                    constructs Submitted, Waiting

                let classify (cost) = {
                    guard cost.value <= 100 else Waiting { cost = cost }
                    Submitted { cost = cost }
                }

                behavior submit : (request: Draft) -> Submitted | Waiting

                let submit (request) = classify(request.cost)

                example submit
                    | (Draft { cost = Amount(50) }) -> Submitted { cost = Amount(50) }
                """;

        assertEquals(MeasurementStatus.UNAVAILABLE, branch(indirect, "classify").status(),
                "nobody wrote a row about `classify`");
        assertEquals(MeasurementStatus.COMPLETE, branch(indirect, "submit").status());
    }

    /** A behavior with no `let` has no arms to go through, which is not the same as arms nothing
     * reaches. */
    @Test
    void aBehaviorWithNoBodyReportsNothingToMeasure() {
        Adequacy.BranchEvidence branch = branch("""
                module example.trip

                data MemberId = String
                data Found = { id: MemberId }
                data Missing = { reason: String }

                behavior findMember : (id: MemberId) -> Found | Missing

                example findMember
                    | (MemberId("m-1")) -> Found { id = MemberId("m-1") }
                """, "findMember");

        assertEquals(MeasurementStatus.UNAVAILABLE, branch.status());
        assertEquals(List.of(), branch.all());
    }

    /** A model nobody wrote a row for is silent, rather than reporting every arm as unreached. */
    @Test
    void aModelWithNoRowsIsSilent() {
        Adequacy.BranchEvidence branch = branch(MODEL, "submit");

        assertEquals(MeasurementStatus.UNAVAILABLE, branch.status());
        assertTrue(unreached(branch).isEmpty());
    }

    // --- one supply of rows -----------------------------------------------------------------------

    /**
     * Everything the report says comes from the same rows.
     *
     * <p>Two evaluations of one model can disagree — a row that timed out under one and held under the
     * other — and a report built half from each could say a case is verified and the arm that produces
     * it is unreached. So the arms are read from the rows the measured classes ran, and so is
     * everything else.
     */
    @Test
    void everyMeasureReadsTheSameRows() {
        String source = MODEL + """

                example submit
                    | (Draft { cost = Amount(500) }) -> Waiting { cost = Amount(500) }
                """;
        Compilation compilation = Compilation.ofSource(source, "Main");
        // Measuring the arms is opted into, so a test about them opts in.
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        String module = compilation.modules().get(0);

        Adequacy.BranchEvidence branch = compilation.db()
                .ask(new Adequacy.BranchCoverage(module)).value().get("submit");
        Adequacy.SignatureEvidence signature = compilation.db()
                .ask(new Adequacy.Witnesses(module)).value().get("submit");

        assertEquals(List.of("then"), unreached(branch));
        assertEquals(1, signature.output().verified().size());
        assertFalse(signature.output().verified().isEmpty(),
                "the arm that ran is the case that was verified");
        assertEquals("Waiting", signature.output().verified().iterator().next().name());
    }
}
