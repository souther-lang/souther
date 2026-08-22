package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.ItemAssessment;
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

    /**
     * A signature with cases to cover and no row to cover them with.
     *
     * <p>Its own model because the measure only reaches {@code NO_ROWS} where every row there is was
     * read: beside a row nobody evaluated, a behavior with no rows is undecided rather than
     * unmeasured, and the shared model above has rows.
     */
    private static final String NO_ROWS = """
            module example.norows

            data Yes
            data No
            data Flag = Yes | No
            data Ask = { flag: Flag }

            data Approved
            data Rejected
            data Verdict = Approved | Rejected

            behavior judge : (q: Ask) -> Verdict
            let judge (q) = Approved
            """;

    /**
     * A measure nobody made says so, whichever measure it is.
     *
     * <p>Silence was the older answer and it is the one this issue is about. A behavior with cases to
     * cover and no row to cover them with had its whole {@code signature} line left out, which reads
     * as a measurement that failed rather than one nobody asked for — and put two behaviors of one
     * report on a different number of lines with nothing saying why.
     */
    @Test
    void aSignatureWithCasesAndNoRowSaysNobodyMeasuredIt() {
        Compilation compilation = Compilation.ofSource(NO_ROWS, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String judge = behaviorBlock(
                AdequacyReport.of(compilation).human(SourceNameResolver.identity()), "judge");

        assertTrue(judge.contains("signature   not measured (no row names this behavior)"), judge);
    }

    private static Compilation compiled() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static String human() {
        return AdequacyReport.of(compiled()).human(SourceNameResolver.identity());
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
                    signature   not applicable (this behavior's output is not a sum)
                    partition   not applicable (the rules of this behavior divide no position)
                      · not derivable: w.v
                    border      not applicable (the rules of this behavior draw no line)
                    branch      not measured (no row names this behavior)
                  narrow                   implemented   rows 0    pending 0
                    signature   not applicable (this behavior's output is not a sum)
                    partition   not applicable (the rules of this behavior divide no position)
                      · not derivable: m.v
                    border      not applicable (the rules of this behavior draw no line)
                    branch      not measured (no row names this behavior)
                  both                     implemented   rows 1    pending 0
                    signature   not applicable (this behavior's output is not a sum)
                    branch      not applicable (this behavior has no body)
                  baseRate                 injected      rows 0    pending 0
                    signature   not applicable (this behavior's output is not a sum)
                    partition   not applicable (the rules of this behavior divide no position)
                    border      borders 2   coverage items 0/0   excluded 4   (4 not measured: no row names this behavior)
                      · no OFF point is owed at r.cost = 0 (invariant Amount #1): excluded — the rules leave no value there
                      · no OUT point is owed at r.cost = 0 (invariant Amount #1): excluded — the rules leave no value there
                      · no OFF point is owed at r.cost = 1000 (invariant Amount #1): excluded — the rules leave no value there
                      · no OUT point is owed at r.cost = 1000 (invariant Amount #1): excluded — the rules leave no value there
                    branch      not applicable (this behavior has no body)
                  rated                    implemented   rows 0    pending 0
                    signature   not applicable (this behavior's output is not a sum)
                    partition   not applicable (the rules of this behavior divide no position)
                    border      borders 2   coverage items 0/0   excluded 4   (4 not measured: no row names this behavior)
                      · no OFF point is owed at r.cost = 0 (invariant Amount #1): excluded — the rules leave no value there
                      · no OUT point is owed at r.cost = 0 (invariant Amount #1): excluded — the rules leave no value there
                      · no OFF point is owed at r.cost = 1000 (invariant Amount #1): excluded — the rules leave no value there
                      · no OUT point is owed at r.cost = 1000 (invariant Amount #1): excluded — the rules leave no value there
                    branch      not measured (no row names this behavior)
                  classify                 implemented   rows 1    pending 0
                    signature   not applicable (this behavior's output is not a sum)
                    partition   axes 1   equivalence partitions 1/2
                      · no row is in `No` at q.flag
                    border      not applicable (the rules of this behavior draw no line)
                    branch      0/0
                  sift                     implemented   rows 0    pending 0
                    signature   not applicable (this behavior's output is not a sum)
                    partition   axes 2   equivalence partitions 0/0   (2 not measured: no row names this behavior)
                    border      not applicable (the rules of this behavior draw no line)
                    branch      not measured (no row names this behavior)

                7 behaviors: 6 implemented, 0 unimplemented, 1 injected; 0 rows waiting for a `let`.
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
        assertTrue(classify.contains("no row is in `No` at q.flag"),
                "the same line is still said where a row was written: " + classify);
    }

    /** How large the space of combinations is says nothing about a behavior no row names, so the
     * numbers are not shown and the reason is. */
    @Test
    void thePairsOfABehaviorNoRowNamesAreNotCountedEither() {
        PartitionEvidence.PairSpace pairs = partitions().get("sift").pairs();
        assertEquals(4, pairs.total(), "two positions of two classes each");
        assertEquals(MeasurementStatus.NOT_MEASURED, pairs.status());
        assertEquals(PartitionEvidence.PairSpace.Reason.NO_ROWS, pairs.reason());
        assertFalse(behaviorBlock(human(), "sift").contains("pairs"),
                "untried is what nobody tried, and nobody was asked");
    }

    /** A composition has no arms of its own. Its stages have them, and it is not asked. */
    @Test
    void aCompositionSaysItsArmsDoNotApply() {
        Adequacy.BranchEvidence branch = branches().get("both");
        assertEquals(MeasurementStatus.NOT_APPLICABLE, branch.status());
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

    /**
     * The two are different answers, and the status says which.
     *
     * <p>A measure with nothing to be about and a measure nobody asked ask opposite things of
     * whoever reads them: the first wants nothing, and the second wants a row written. Held as one
     * status apart by each measure's own reason, only a reader that knows that measure's reasons can
     * tell them apart — so every reader that has to rebuilt it, and a measure whose reasons nobody
     * had in mind was read as whichever the rebuild happened to favour.
     */
    @Test
    void aMeasureThatDoesNotApplyIsNotTheSameStatusAsOneNobodyMade() {
        assertNotEquals(branches().get("rated").status(), branches().get("both").status(),
                "a body no row names and a composition with no arms are not one answer");
    }

    /** A line an invariant drew is met by writing the value, so it is never waiting on the arms.
     * The two origins are measured along separate paths for exactly this reason. */
    @Test
    void anInvariantsLineIsNeverWaitingOnTheArms() {
        List<BorderAssessment.Point> lines =
                BorderAssessment.pointsOf(partitions().get("rated").boundaries()).stream()
                        .filter(p -> p.owed() != null).toList();
        assertFalse(lines.isEmpty(), "the invariant draws two");
        for (BorderAssessment.Point line : lines) {
            assertEquals(ItemAssessment.Coverage.Reason.NO_ROWS, line.item().whyNotMeasured(),
                    line.border().rule().named() + " at " + line.asked());
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
        compilation.measure(Adequacy.Asked.fullReport());
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
        for (BorderAssessment.Point line : BorderAssessment.pointsOf(partition.boundaries())) {
            if (line.owed() == null) {
                continue;   // nothing was measured there and nothing was waiting on a row
            }
            assertNotEquals(ItemAssessment.Coverage.Reason.NO_ROWS, line.item().whyNotMeasured(),
                    line.border().rule().named() + " at " + line.asked());
            assertEquals(MeasurementStatus.PARTIAL, line.item().status(),
                    line.border().rule().named() + " at " + line.asked());
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
     * A measure that answers with a number, or with which of the two kinds of no-number it is.
     *
     * <p>There is no fifth state and no way to build one: the reason a measure gives says which kind
     * it is, and a measure with a number has no reason to give. Held over every measure of the model
     * rather than over the ones a test remembered, so that a measure added later is in it.
     */
    @Test
    void everyMeasureAnswersWithANumberOrWithWhichKindOfNoNumber() {
        List<Object[]> measures = allMeasures();
        assertTrue(measures.size() > 20, "the model produces every kind: " + measures.size());
        for (Object[] measure : measures) {
            MeasurementStatus status = (MeasurementStatus) measure[1];
            souther.compiler.observe.MeasureReason reason =
                    (souther.compiler.observe.MeasureReason) measure[2];
            if (status.counted()) {
                assertNull(reason, measure[0] + " has a number and says why it has none");
            } else {
                assertNotNull(reason, measure[0] + " has no number and does not say why");
                assertEquals(status, reason.status(),
                        measure[0] + " is one kind of no-number and its reason is the other");
            }
        }
    }

    /**
     * What the verdict does with each kind.
     *
     * <p>The two are the whole reason for telling them apart. A measure nothing was ever going to be
     * measured at is not a doubt anybody can act on; a measure that could have found a gap and was
     * not made is exactly one. Asked of one model holding both, so that neither answer is the
     * accident of a fixture with only one kind in it.
     */
    @Test
    void aMeasureThatWasNotMadeHoldsTheVerdictOpenAndAnInapplicableOneDoesNot() {
        AdequacyReport report = AdequacyReport.of(compiled());
        assertEquals(AdequacyReport.AdequacyStatus.UNDETERMINED, report.adequacy(),
                report.human(SourceNameResolver.identity()));

        List<Object[]> measures = allMeasures();
        assertTrue(measures.stream().anyMatch(m -> m[1] == MeasurementStatus.NOT_APPLICABLE),
                "the model holds an inapplicable measure");
        assertTrue(measures.stream().anyMatch(m -> m[1] == MeasurementStatus.NOT_MEASURED),
                "and one nobody made");

        // Every behavior of the model whose signature does not apply still reads `satisfied` where
        // the measures that were asked came to an answer — the inapplicable ones are not what holds
        // this open. `classify` is the one whose positions were divided and whose arms were run.
        String classify = behaviorBlock(human(), "classify");
        assertTrue(classify.contains("not applicable"), classify);
        assertTrue(classify.contains("branch      0/0"), classify);
    }

    /** Every measure the model produces, as (what it is, its status, its reason). */
    private static List<Object[]> allMeasures() {
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
            measures.add(new Object[] {"partition " + each.getKey(),
                    partition.partitioned().status(), partition.partitioned().reason()});
            measures.add(new Object[] {"boundary " + each.getKey(),
                    partition.bounded().status(), partition.bounded().reason()});
            measures.add(new Object[] {"pairs " + each.getKey(),
                    partition.pairs().status(), partition.pairs().reason()});
            partition.axes().forEach(a -> measures.add(
                    new Object[] {"axis " + each.getKey(), a.status(), a.reason()}));
            BorderAssessment.pointsOf(partition.boundaries()).stream()
                    .filter(p -> p.owed() != null)
                    .forEach(p -> measures.add(new Object[] {"line " + each.getKey(),
                            p.item().status(), p.item().whyNotMeasured()}));
        }
        return measures;
    }

    /**
     * Held where the value is built, so that no measure can be assembled without it.
     *
     * <p>The two measures whose evidence is a list keep it by shape now rather than by check: an
     * answer that has entries is an arm that carries them and an answer that has none is an arm
     * with nowhere to put any, so a status paired with the wrong list is not a value anybody can
     * write. What is left to assert of them is the one pairing the arms could still get wrong —
     * an arm that promises entries and holds none.
     */
    @Test
    void aMeasureCannotBeBuiltWithoutKeepingThatContract() {
        assertThrows(IllegalStateException.class,
                () -> new souther.compiler.query.PartitionDerivation.Complete(List.of()));
        assertThrows(IllegalStateException.class,
                () -> new souther.compiler.query.PartitionDerivation.Partial(List.of()));
        assertThrows(IllegalStateException.class,
                () -> new souther.compiler.query.BoundaryDerivation.Complete(List.of()));
        assertThrows(IllegalStateException.class,
                () -> new souther.compiler.query.BoundaryDerivation.Partial(List.of()));
        // And a space this could not walk to the end of, called measured in full. The flag and
        // the status are one answer, and while the two could disagree a reader that noticed
        // stopped trusting the status and decided it again — which is a second authority over one
        // measure.
        assertThrows(IllegalArgumentException.class, () -> new PartitionEvidence.PairSpace(
                9, 0, 0, 0, 9, true, MeasurementStatus.COMPLETE, null));
        // And an absence that nothing proved. The proof is the argument, so this is the whole of
        // what "the model divides nothing anywhere" costs to say.
        assertThrows(NullPointerException.class,
                () -> new souther.compiler.query.PartitionDerivation.Absent(null));
        assertThrows(NullPointerException.class,
                () -> new souther.compiler.query.BoundaryDerivation.Absent(null));
        assertThrows(IllegalArgumentException.class, () -> new Adequacy.BranchEvidence(
                List.of(), java.util.Set.of(), java.util.Set.of(),
                MeasurementStatus.NOT_MEASURED, MeasurementStatus.NOT_MEASURED, null));
        assertThrows(IllegalArgumentException.class, () -> new Adequacy.BranchEvidence(
                List.of(), java.util.Set.of(), java.util.Set.of(),
                MeasurementStatus.COMPLETE, MeasurementStatus.COMPLETE,
                Adequacy.BranchEvidence.Reason.NO_BODY));
        assertThrows(IllegalArgumentException.class, () -> new PartitionEvidence.AxisCoverage(
                "a", "a", List.of(), java.util.Set.of(), 0, MeasurementStatus.NOT_MEASURED, null,
                PartitionEvidence.AxisCoverage.ANSWERED));
        // And a position handed over with no account of what was read about its values. The classes
        // beside it mean one thing on a reading that ran to the end and another on one that did
        // not, so a coverage that does not say which is a set of classes nobody can read.
        assertThrows(IllegalArgumentException.class, () -> new PartitionEvidence.AxisCoverage(
                "a", "a", List.of(), java.util.Set.of(), 0, MeasurementStatus.COMPLETE, null,
                null));

        // The kinds are held against each other and not only for presence. A measure carrying a
        // reason of the other kind is the confusion the two words were split to prevent: it says its
        // arms do not apply and asks somebody to go and measure them, and a report reading either
        // half of it is right about one and wrong about the other.
        assertThrows(IllegalArgumentException.class, () -> new Adequacy.BranchEvidence(
                List.of(), java.util.Set.of(), java.util.Set.of(),
                MeasurementStatus.NOT_MEASURED, MeasurementStatus.NOT_MEASURED,
                Adequacy.BranchEvidence.Reason.NO_BODY));
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
