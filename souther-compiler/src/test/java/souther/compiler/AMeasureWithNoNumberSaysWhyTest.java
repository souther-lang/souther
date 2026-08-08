package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.BoundaryAssessment;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Why a measure has no number, kept by the measure and not worked out again downstream.
 *
 * <p>Every one of these has the same shape underneath. A measure came back with nothing, the reason
 * was not carried with it, and whatever read it next rebuilt the reason out of what else was to
 * hand — the row count, whether the behavior was injected, whether the declaration had a body. Those
 * correlate with the reason and are not it, so each rebuild was right about the cases it was written
 * against and wrong about one nobody had in mind.
 */
class AMeasureWithNoNumberSaysWhyTest {

    /**
     * One model holding each way a measure can come back empty.
     *
     * <p>Together in one module on purpose: what the report says about any one of these is only
     * right if it is still right beside the others, and the run that measures them is the same run.
     */
    private static final String MODEL = """
            module example.repro

            data Wrap = { v: String }
            data Mid = { v: String }
            data Out = { v: String }

            behavior widen : (w: Wrap) -> Mid constructs Mid
            let widen (w) = Mid { v = w.v }
            behavior narrow : (m: Mid) -> Out constructs Out
            let narrow (m) = Out { v = m.v }

            behavior both = widen >-> narrow

            example both
                | (Wrap { v = "x" }) -> Out { v = "x" }

            data Amount = Int
                invariant value >= 0 && value <= 1000

            data Req = { cost: Amount }
            data Res = { n: Int }

            behavior baseRate : (r: Req) -> Res
                constructs Res

            behavior rated : (r: Req) -> Res
                constructs Res
            let rated (r) = Res { n = r.cost.value }

            data Yes
            data No
            data Flag = Yes | No
            data Ask = { flag: Flag }

            behavior classify : (q: Ask) -> Res
                constructs Res
            let classify (q) = Res { n = 1 }

            example classify
                | (Ask { flag = Yes }) -> Res { n = 1 }

            data Pair = { left: Flag, right: Flag }

            behavior sift : (p: Pair) -> Res
                constructs Res
            let sift (p) = Res { n = 0 }
            """;

    private static Compilation compiled() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return compilation;
    }

    private static String human() {
        return AdequacyReport.of(compiled()).human();
    }

    /**
     * The whole report, fixed.
     *
     * <p>Fixed whole rather than line by line. Every wrong line this issue was about could have been
     * removed by printing less, and a test that only forbids the wrong sentences passes on a report
     * that says nothing at all. What each behavior is told about it is here to be read.
     */
    @Test
    void theReportSaysWhatEachMeasureManagedAndWhyWhereItManagedNothing() {
        assertEquals("""
                example.repro                                            measurement: complete
                  widen                    implemented   rows 0    pending 0
                    partition   axes 0   single-axis 0/0
                    boundary    0/0
                      · not derivable: w.v
                  narrow                   implemented   rows 0    pending 0
                    partition   axes 0   single-axis 0/0
                    boundary    0/0
                      · not derivable: m.v
                  both                     implemented   rows 1    pending 0
                    branch      not applicable (this behavior has no body)
                  baseRate                 injected      rows 0    pending 0
                    partition   axes 0   single-axis 0/0
                    boundary    0/0   (2 not measured: no row names this behavior)
                    branch      not applicable (this behavior has no body)
                  rated                    implemented   rows 0    pending 0
                    partition   axes 0   single-axis 0/0
                    boundary    0/0   (2 not measured: no row names this behavior)
                  classify                 implemented   rows 1    pending 0
                    partition   axes 1   single-axis 1/2
                      · no row is in `No`
                    boundary    0/0
                    branch      0/0
                  sift                     implemented   rows 0    pending 0
                    partition   axes 2   single-axis 0/0   (2 not measured: no row names this behavior)
                    boundary    0/0

                7 behaviors: 6 implemented, 1 injected; 0 rows waiting for a `let`.
                adequacy: undetermined
                """, human());
    }

    /** What the report may not say, checked over the whole of it: a line removed from one behavior
     * and left on another is the defect, not the fix. */
    @Test
    void nothingSaysAMeasurementIsStillComing() {
        String human = human();
        assertFalse(human.contains("until branches are"), human);
        assertFalse(human.contains("were not measured"), human);
    }

    /**
     * A behavior no row names has no gaps to be told about.
     *
     * <p>An absence of evidence is not a set of gaps, and naming the classes nothing sits in sends an
     * author after rows on the strength of a measurement nobody made. Asked of {@code sift}, which
     * has positions the model divides and no row at any of them — a behavior with no positions at all
     * would pass this whatever the code did.
     */
    @Test
    void aBehaviorNoRowNamesIsNotToldWhichClassesItMisses() {
        PartitionEvidence partition = partitions().get("sift");
        assertEquals(2, partition.axes().size(), "the model divides two positions here");
        for (PartitionEvidence.AxisCoverage axis : partition.axes()) {
            assertEquals(2, axis.classes().size(), axis.path());
            assertEquals(PartitionEvidence.AxisCoverage.Reason.NO_ROWS, axis.reason(), axis.path());
        }
        assertEquals(List.of(), findings("sift", Adequacy.Kind.AXIS_CLASS_UNCOVERED),
                "nothing was established, so nothing was found");

        String sift = behaviorBlock(human(), "sift");
        assertFalse(sift.contains("no row is in"), sift);
        String classify = behaviorBlock(human(), "classify");
        assertTrue(classify.contains("no row is in `No`"),
                "the same line is still said where a row was written: " + classify);
    }

    /** How large the space of combinations is says nothing about a behavior no row names, so the
     * numbers are not shown and the reason is. */
    @Test
    void thePairsOfABehaviorNoRowNamesAreNotCountedEither() {
        PartitionEvidence.PairSpace pairs = partitions().get("sift").pairs();
        assertEquals(4, pairs.total(), "two positions of two classes each");
        assertEquals(MeasurementStatus.UNAVAILABLE, pairs.status());
        assertEquals(PartitionEvidence.PairSpace.Reason.NO_ROWS, pairs.reason());
        assertFalse(behaviorBlock(human(), "sift").contains("pairs"),
                "untried is what nobody tried, and nobody was asked");
    }

    /** A composition has no arms of its own. Its stages have them, and it is not asked. */
    @Test
    void aCompositionSaysItsArmsDoNotApply() {
        Adequacy.BranchEvidence branch = branches().get("both");
        assertEquals(MeasurementStatus.UNAVAILABLE, branch.status());
        assertEquals(Adequacy.BranchEvidence.Reason.NO_BODY, branch.reason());
        assertFalse(branch.applicable(), "nothing here is owed a branch measure");
    }

    /** An injected behavior has none either, and it is the body and not the `let` that decides:
     * the composition above is implemented and has no body all the same. */
    @Test
    void anInjectedBehaviorSaysTheSame() {
        Adequacy.BranchEvidence branch = branches().get("baseRate");
        assertEquals(Adequacy.BranchEvidence.Reason.NO_BODY, branch.reason());
    }

    /** A body with arms, that no row names, is a measure that was not made rather than one that does
     * not apply. The verdict reads these apart. */
    @Test
    void aBodyNoRowNamesIsUnmeasuredAndNotInapplicable() {
        Adequacy.BranchEvidence branch = branches().get("rated");
        assertEquals(Adequacy.BranchEvidence.Reason.NO_ROWS, branch.reason());
        assertTrue(branch.applicable(), "there are arms here; nothing asked about them");
    }

    /** A line an invariant drew is met by writing the value, so it is never waiting on the arms.
     * The two origins are measured along separate paths for exactly this reason. */
    @Test
    void anInvariantsLineIsNeverWaitingOnTheArms() {
        List<BoundaryAssessment> lines = partitions().get("rated").boundaries();
        assertFalse(lines.isEmpty(), "the invariant draws two");
        for (BoundaryAssessment line : lines) {
            assertEquals(BoundaryAssessment.Coverage.Reason.NO_ROWS, line.reason(),
                    line.origin() + " at " + line.value());
        }
    }

    /**
     * A source that could not be evaluated, holding the only rows one behavior has.
     *
     * <p>The attached file redeclares a name the module already declares, so it does not evaluate.
     * `take` keeps the row written beside it; `elsewhere` has every row it owns in there, and what
     * comes back for it is an empty list of rows and a reason saying the list is not the model's.
     */
    private static final List<String> UNSEEN = List.of("""
            module example.unseen

            data Amount = Int
                invariant value >= 0 && value <= 1000

            data Yes
            data No
            data Flag = Yes | No

            data Draft = { cost: Amount, flag: Flag }
            data Ok = { n: Int }

            let shared = Draft { cost = Amount(7), flag = Yes }

            behavior take : (request: Draft) -> Ok
                constructs Ok
            let take (request) = Ok { n = request.cost.value }

            behavior elsewhere : (request: Draft) -> Ok
                constructs Ok
            let elsewhere (request) = {
                guard request.cost.value <= 100 else Ok { n = 0 }
                Ok { n = request.cost.value }
            }

            example take
                | (Draft { cost = Amount(7), flag = Yes }) -> Ok { n = 7 }
            """, """
            examples for example.unseen

            let shared = Draft { cost = Amount(0), flag = No }

            example elsewhere
                | (Draft { cost = Amount(0), flag = No }) -> Ok { n = 0 }
            """);

    private static Compilation unseen() {
        Compilation compilation = Compilation.ofSources(UNSEEN,
                souther.compiler.meta.ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return compilation;
    }

    /**
     * No rows to read and no rows are two different things.
     *
     * <p>A behavior nobody wrote a row for is not being asked. A behavior whose rows are in a source
     * that would not evaluate is being asked and cannot be answered, and the rows it is waiting on may
     * already be written. Calling the second `no_rows` tells an author to write what is sitting in the
     * file the run could not read — which is the mistake this whole change is about, made once more
     * about a different pair of correlated states.
     */
    @Test
    void rowsNothingCouldReadAreNotRowsThatWereNeverWritten() {
        Compilation compilation = unseen();
        AdequacyReport.BehaviorReport reported = AdequacyReport.of(compilation)
                .modules().get(0).behaviors().stream()
                .filter(b -> b.name().equals("elsewhere")).findFirst().orElseThrow();
        assertEquals(0, reported.rows(), "nothing was read");
        assertTrue(AdequacyReport.of(compilation).modules().get(0).incompleteness().stream()
                        .anyMatch(gap -> gap.code() == Incompleteness.Code.OBSERVATION_ABSENT),
                "and there may well have been something to read");

        Adequacy.BranchEvidence branch = compilation.db()
                .ask(new Adequacy.BranchCoverage("example.unseen")).value().get("elsewhere");
        assertNotEquals(Adequacy.BranchEvidence.Reason.NO_ROWS, branch.reason(),
                "the rows this is waiting on may be the ones that went unread");
        assertEquals(MeasurementStatus.PARTIAL, branch.status(),
                "there are arms, and which of them were reached is undecided");

        PartitionEvidence partition = compilation.db()
                .ask(new Adequacy.Coverage("example.unseen")).value().get("elsewhere");
        assertFalse(partition.boundaries().isEmpty(), "the invariant and the guard draw lines");
        for (BoundaryAssessment line : partition.boundaries()) {
            assertNotEquals(BoundaryAssessment.Coverage.Reason.NO_ROWS, line.reason(),
                    line.origin() + " at " + line.value());
            assertEquals(MeasurementStatus.PARTIAL, line.status(),
                    line.origin() + " at " + line.value());
        }
    }

    /** The behavior beside it, whose own row was read, still answers from what was read. */
    @Test
    void aBehaviorWhoseRowsWereReadIsUnaffectedByTheSourceThatWasNot() {
        Adequacy.BranchEvidence branch = unseen().db()
                .ask(new Adequacy.BranchCoverage("example.unseen")).value().get("take");
        assertNull(branch.reason(), "this one was measured");
    }

    /**
     * The contract, both ways, over every measure the model produced.
     *
     * <p>Both ways because one way alone lets the opposite mistake in. Without the first a measure
     * can go back to coming home empty and silent; without the second a measure can carry a reason
     * beside a number, which says a value is missing and gives it in the same breath.
     */
    @Test
    void aMeasureWithNoNumberSaysWhyAndOneWithANumberDoesNot() {
        List<Object[]> measures = new ArrayList<>();
        for (Map.Entry<String, Adequacy.BranchEvidence> each : branches().entrySet()) {
            measures.add(new Object[] {"branch " + each.getKey(),
                    each.getValue().status(), each.getValue().reason()});
        }
        for (Map.Entry<String, Adequacy.SignatureEvidence> each : signatures().entrySet()) {
            measures.add(new Object[] {"signature " + each.getKey(),
                    each.getValue().status(), each.getValue().reason()});
            measures.add(new Object[] {"out " + each.getKey(),
                    each.getValue().output().status(), each.getValue().output().reason()});
            each.getValue().inputs().forEach(in -> measures.add(
                    new Object[] {"in " + each.getKey(), in.status(), in.reason()}));
        }
        for (Map.Entry<String, PartitionEvidence> each : partitions().entrySet()) {
            PartitionEvidence partition = each.getValue();
            measures.add(new Object[] {"pairs " + each.getKey(),
                    partition.pairs().status(), partition.pairs().reason()});
            partition.axes().forEach(a -> measures.add(
                    new Object[] {"axis " + each.getKey(), a.status(), a.reason()}));
            partition.boundaries().forEach(b -> measures.add(
                    new Object[] {"boundary " + each.getKey(), b.status(), b.reason()}));
        }
        assertTrue(measures.size() > 20, "the model produces every kind: " + measures.size());
        for (Object[] measure : measures) {
            if (measure[1] == MeasurementStatus.UNAVAILABLE) {
                assertNotNull(measure[2], measure[0] + " has no number and does not say why");
            } else {
                assertNull(measure[2], measure[0] + " has a number and says why it has none");
            }
        }
    }

    /** Held where the value is built, so that no measure can be assembled without it. */
    @Test
    void aMeasureCannotBeBuiltWithoutKeepingThatContract() {
        assertThrows(IllegalArgumentException.class, () -> new Adequacy.BranchEvidence(
                List.of(), java.util.Set.of(), java.util.Set.of(),
                MeasurementStatus.UNAVAILABLE, null));
        assertThrows(IllegalArgumentException.class, () -> new Adequacy.BranchEvidence(
                List.of(), java.util.Set.of(), java.util.Set.of(),
                MeasurementStatus.COMPLETE, Adequacy.BranchEvidence.Reason.NO_BODY));
        assertThrows(IllegalArgumentException.class, () -> new PartitionEvidence.AxisCoverage(
                "a", "a", List.of(), java.util.Set.of(), List.of(), 0,
                MeasurementStatus.UNAVAILABLE, null));
    }

    private static String behaviorBlock(String human, String behavior) {
        List<String> kept = new ArrayList<>();
        boolean inside = false;
        for (String line : human.lines().toList()) {
            if (line.startsWith("  ") && !line.startsWith("    ") && !line.startsWith("      ")) {
                inside = line.trim().startsWith(behavior + " ");
            }
            if (inside) {
                kept.add(line);
            }
        }
        assertFalse(kept.isEmpty(), behavior + " is in the report");
        return String.join("\n", kept);
    }

    private static Map<String, Adequacy.BranchEvidence> branches() {
        Compilation compilation = compiled();
        return compilation.db()
                .ask(new Adequacy.BranchCoverage(compilation.modules().get(0))).value();
    }

    private static Map<String, PartitionEvidence> partitions() {
        Compilation compilation = compiled();
        return compilation.db().ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
    }

    private static List<Adequacy.Finding> findings(String behavior, Adequacy.Kind kind) {
        Compilation compilation = compiled();
        Map<String, List<Adequacy.Finding>> all = compilation.db()
                .ask(new Adequacy.Findings(compilation.modules().get(0))).value();
        return all.getOrDefault(behavior, List.of()).stream()
                .filter(f -> f.kind() == kind).toList();
    }

    private static Map<String, Adequacy.SignatureEvidence> signatures() {
        Compilation compilation = compiled();
        return compilation.db().ask(new Adequacy.Witnesses(compilation.modules().get(0))).value();
    }
}
