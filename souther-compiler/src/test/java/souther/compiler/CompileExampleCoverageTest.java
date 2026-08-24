package souther.compiler;

import souther.compiler.report.AdequacyReport;
import souther.compiler.source.SourceId;

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
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, Adequacy.BranchEvidence> all = compilation.db()
                .ask(new Adequacy.BranchCoverage(compilation.modules().get(0))).value();
        assertNotNull(all, "the model under test compiles");
        return all.get(behavior);
    }

    private static List<String> unreached(Adequacy.BranchEvidence branch) {
        return branch.unreached().orElseThrow().stream()
                .map(souther.compiler.report.ArmVocabulary::label).toList();
    }

    /** One row through the guard leaves the other arm with nothing going through it. */
    @Test
    void anArmNoRowGoesThroughIsNamed() {
        Adequacy.BranchEvidence branch = branch(MODEL + """

                example submit
                    | (Draft { cost = Amount(50) }) -> Submitted { cost = Amount(50) }
                """, "submit");

        assertEquals(MeasurementStatus.COMPLETE, AdequacyReport.statusOf(branch.measured()));
        assertEquals(2, branch.arms().all().size(), "a guard is two arms");
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
        assertEquals(2, branch.arms().covered().size());
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

        assertEquals(2, branch.arms().all().size(), "two arms, though there are three cases");
        assertEquals(List.of("case Overseas"), unreached(branch));
    }

    /**
     * An arm that answers {@code unreachable} is not an arm, so a model that says where its
     * combinations cannot arise can still reach every arm it has.
     *
     * <p>Reaching one is already E1911, so counting it would leave such a model permanently one arm
     * short and reward inventing a fallback answer over stating the premise.
     */
    @Test
    void anArmThatAnswersUnreachableIsNotOneARowIsOwedFor() {
        Adequacy.BranchEvidence branch = branch("""
                module example.probe

                data On
                data Off
                data Flag = On | Off
                data Answer = Int

                behavior pick : (f: Flag) -> Answer
                    constructs Answer

                let pick (f) = match f with
                    | On  -> Answer(1)
                    | Off -> unreachable "the probe only ever passes On"

                example pick
                    | "on" : (On) -> Answer(1)
                """, "pick");

        assertEquals(1, branch.arms().all().size(), "one arm, not two");
        assertEquals(List.of(), unreached(branch));
    }

    /**
     * The arm that is left keeps its own probe, whichever side of the missing one it is written.
     *
     * <p>The emitter asks for a node's arms as an array and indexes it by the arm's position. Were
     * the arm that answers nothing dropped from that array rather than left empty in it, the arm
     * below would take its number and light the wrong probe — and the count would still be one, so
     * nothing downstream could see it. Here the surviving arm is written second, so it is the second
     * entry that has to hold the probe.
     */
    @Test
    void theArmAfterAnUnreachableOneIsStillItself() {
        Adequacy.BranchEvidence branch = branch("""
                module example.probe

                data On
                data Off
                data Flag = On | Off
                data Answer = Int

                behavior pick : (f: Flag) -> Answer
                    constructs Answer

                let pick (f) = match f with
                    | On  -> unreachable "the probe never passes On"
                    | Off -> Answer(0)

                example pick
                    | "off" : (Off) -> Answer(0)
                """, "pick");

        assertEquals(List.of("case Off"),
                branch.arms().all().stream().map(site -> souther.compiler.report.ArmVocabulary.label(site)).toList());
        assertEquals(List.of(), unreached(branch), "the row went through the arm that is left");
    }

    /**
     * A fork behind an abort is measured through a real compile, not only in the plan.
     *
     * <p>The arms are dropped from the count and the fork stays in the plan without them, and it is
     * the emitter that says whether those two agree: it generates the bytecode of the body that
     * aborts like any other and asks for the arms of every fork it passes. A plan that dropped the
     * fork instead of emptying it stops the generation here rather than in a unit test.
     */
    @Test
    void aForkNothingReachesIsNeitherCountedNorLostFromThePlan() {
        Adequacy.BranchEvidence branch = branch("""
                module example.dead

                data Yes
                data No
                data Answer = Yes | No

                data Score = Int

                behavior scoreFor : (a: Answer, b: Answer) -> Score
                    constructs Score

                let scoreFor (a, b) =
                    match a with
                        | Yes -> Score(1)
                        | No  -> {
                            let impossible: Int = unreachable "no No arrives"
                            match b with
                                | Yes -> Score(impossible)
                                | No  -> Score(3)
                        }

                example scoreFor
                    | "yes" : (Yes, Yes) -> Score(1)
                """, "scoreFor");

        assertEquals(1, branch.arms().all().size(), "one arm a row can be in, not three");
        assertEquals(List.of(), unreached(branch));
        assertEquals(MeasurementStatus.COMPLETE, AdequacyReport.statusOf(branch.measured()));
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
                .withDeadline(DoesNotComeBack.overrunningOn(DoesNotComeBack.everyRowOf("go")));
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        SourceId sourceId = compilation.exampleSourcesOf(module).getFirst();
        List<souther.compiler.observe.RowOutcome> rows = compilation.db()
                .ask(souther.compiler.query.Output.Examples.asked(
                        compilation.db(), module, sourceId)).value().rows();

        assertEquals(1, rows.size());
        assertEquals(souther.compiler.observe.Disposition.INCOMPLETE, rows.get(0).disposition(),
                "the row is the one that never came back");
        assertEquals(souther.compiler.observe.FailurePhase.TIMEOUT, rows.get(0).failurePhase());
        assertEquals(new souther.compiler.observe.Applied.Nothing(), rows.get(0).run().applied(),
                "the deadline gave the row up before the behavior was applied");
        assertEquals(new souther.compiler.observe.Counting.Unread(), rows.get(0).run().counting(),
                "and what it spent on the way was never read, which is not the same as nothing");

        Adequacy.BranchEvidence branch = compilation.db()
                .ask(new Adequacy.BranchCoverage(module)).value().get("go");
        assertEquals(2, branch.arms().all().size(), "the arms are there to reach");
        assertEquals(List.of(), branch.arms().covered().stream().sorted().toList(),
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

        assertEquals(MeasurementStatus.NOT_MEASURED, AdequacyReport.statusOf(branch(indirect, "classify").measured()),
                "nobody wrote a row about `classify`");
        // And the row's own behavior forks nowhere, so it owes no arm rather than owing none of the
        // arms it ran through. What the row reached belongs to the behavior whose arm it is.
        assertEquals(MeasurementStatus.NOT_APPLICABLE,
                AdequacyReport.statusOf(branch(indirect, "submit").measured()));
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

        assertEquals(MeasurementStatus.NOT_APPLICABLE, AdequacyReport.statusOf(branch.measured()));
        // No arms, and not an empty list of them. A behavior with no body is a measure that does not
        // apply, so there is nothing here to count — which used to come back as an empty collection
        // and a zero, and read like a body every arm of which went unreached (issue #997).
        assertTrue(branch.measured().made().isEmpty(),
                () -> "a measure that does not apply has no value: " + branch.measured());
    }

    /** A model nobody wrote a row for is silent, rather than reporting every arm as unreached. */
    @Test
    void aModelWithNoRowsIsSilent() {
        Adequacy.BranchEvidence branch = branch(MODEL, "submit");

        assertEquals(MeasurementStatus.NOT_MEASURED, AdequacyReport.statusOf(branch.measured()));
        // Silent, and that is the absence of a value rather than an empty answer. Which arms no row
        // reaches is a claim about the rows there were, and there were none to read.
        assertTrue(branch.unreached().isEmpty(),
                () -> "nothing was measured, so no arm can be named unreached: "
                        + branch.measured());
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
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().get(0);

        Adequacy.BranchEvidence branch = compilation.db()
                .ask(new Adequacy.BranchCoverage(module)).value().get("submit");
        Adequacy.SignatureEvidence signature = compilation.db()
                .ask(new Adequacy.Witnesses(module)).value().get("submit");

        // The `guard` passes into the rest of the block, and the author wrote no `then` for it
        // to be called after.
        assertEquals(List.of("continued"), unreached(branch));
        assertEquals(1, signature.output().seen().verified().size());
        assertFalse(signature.output().seen().verified().isEmpty(),
                "the arm that ran is the case that was verified");
        assertEquals("Waiting", signature.output().seen().verified().iterator().next().name());
    }
}
