package souther.compiler.report;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.observe.RowIdentity;
import souther.compiler.observe.RowRef;
import souther.compiler.query.Adequacy;
import souther.compiler.query.InputCaseEvidence;
import souther.compiler.query.Measurement;
import souther.compiler.query.OutputCaseEvidence;
import souther.compiler.query.Weakening;
import souther.compiler.query.WeakeningSet;
import souther.compiler.source.SourceId;
import souther.compiler.types.TypeSymbol;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row whose case cannot be read from its text leaves undecided a case no row is counted at, and
 * nothing else (example-adequacy).
 *
 * <p>Which sets of the measure the row could have joined is what decides it. An input row that got
 * as far as being applied and held would join all three, so a case missing from any of them may be
 * the row's; a row whose sets already hold every case decides nothing by being read.
 *
 * <p>Through the compiler and not by building the measure. Which sets a row joins is decided where
 * the rows are counted, and a measure handed sets by a test says nothing about that.
 */
class ARowWhoseCaseIsNotReadLeavesUndecidedOnlyACaseNoRowIsCountedAtTest {

    /** The model of the issue, with the rows put in by each case. {@code hit(0)} is a helper's
     *  answer, which names no case. At {@code 0} so that the line the invariant draws has its row
     *  whichever rows beside it a case puts in: what is asked here is the case measure, and a
     *  point no row is at would refuse the verdict over something else. */
    private static String model(String rows) {
        return """
                module m

                data Shot = Hit | Miss

                data Hit = Int
                    invariant value >= 0

                behavior record : (bonus: Int, shot: Shot) -> Int

                let record (bonus, shot) =
                    match shot with
                        | Hit as h -> h.value + bonus
                        | Miss -> bonus

                let hit (n: Int): Shot = Hit(n)

                example record
                """ + rows;
    }

    private static final String A_HIT_BY_A_HELPER = "    | \"a hit\" : (0, hit(0)) -> 0\n";
    private static final String A_MISS = "    | \"a miss\" : (0, Miss) -> 0\n";

    private static InputCaseEvidence theShot(AdequacyReport report) {
        Adequacy.SignatureEvidence signature = report.modules().getFirst().behaviors().stream()
                .filter(each -> each.name().equals("record"))
                .findFirst().orElseThrow().signature();
        return signature.inputs().made().orElseThrow().get(1);
    }

    private static RowRef aHit(AdequacyReport report) {
        return theRow(report, "a hit");
    }

    private static RowRef theRow(AdequacyReport report, String name) {
        return report.modules().getFirst().behaviors().getFirst().reading().rowsSeen().stream()
                .map(RowRef::of)
                .filter(each -> each.identity().equals(new RowIdentity.Named(name)))
                .findFirst().orElseThrow();
    }

    /** Every case has a row that names it, so the row the helper wrote decides nothing. */
    @Test
    void everyCaseNamedLeavesTheMeasureCompleteAndTheVerdictSatisfied() {
        AdequacyReport report = WrittenWitness.reportOf(model(A_HIT_BY_A_HELPER
                + "    | \"a hit of three\" : (0, Hit(3)) -> 3\n" + A_MISS));
        InputCaseEvidence shot = theShot(report);

        assertEquals(1, shot.seen().unclassifiedRows(), "the helper's row is still not read");
        assertInstanceOf(Measurement.Complete.class, shot.cases(),
                () -> "every case has a row naming it, and it says " + shot.cases());
        assertEquals(AdequacyReport.AdequacyStatus.SATISFIED, report.adequacy(),
                () -> "and nothing else holds it open: " + report.whatKeepsTheVerdictOpen());
    }

    /**
     * With no row naming {@code Hit}, the helper's rows may be the ones covering it, and the line
     * holding the verdict open names the input as the signature does and sends a reader to the
     * rows. Two of them, the second at a value above the line, because the region above it and
     * the {@code Hit} arm answering as the {@code Miss} arm are owed a row and would refuse the
     * verdict without one.
     */
    @Test
    void aCaseNoRowNamesIsUndecidedAndTheLineNamesTheRowsAndTheInput() {
        AdequacyReport report = WrittenWitness.reportOf(model(A_HIT_BY_A_HELPER
                + "    | \"a hit of three\" : (0, hit(3)) -> 3\n" + A_MISS));
        InputCaseEvidence shot = theShot(report);
        List<RowRef> rows = List.of(aHit(report), theRow(report, "a hit of three"));

        Measurement.Partial<?> partial = assertInstanceOf(Measurement.Partial.class, shot.cases());
        assertEquals(List.of(new Weakening.InputCasesUnreadable("record", 1, Set.copyOf(rows))),
                List.copyOf(partial.weakening().causes()));
        assertEquals(AdequacyReport.AdequacyStatus.UNDETERMINED, report.adequacy(),
                () -> "a case the helper's row may cover is refused over: "
                        + report.adequacyGaps());

        AdequacyUncertainty open = report.whatKeepsTheVerdictOpen().stream()
                .filter(each -> each instanceof AdequacyUncertainty.ByWeakening it
                        && it.cause() instanceof Weakening.InputCasesUnreadable)
                .findFirst().orElseThrow();
        assertEquals(new ReaderDisposition.WriteTheCaseOutIn(
                new Subject.AtAnInput("record", 1), Set.copyOf(rows)), ReaderDisposition.of(open));

        SourceRendering rendering = SourceRendering.namedByIdentity(SourceLayouts.NONE);
        String human = report.human(rendering);
        assertTrue(human.contains("in #2 specified 1/2"), human);
        assertTrue(human.contains("input #2 of record — the rows "
                        + rows.getFirst().shown(rendering.names().nameOf(rows.getFirst().source()))
                        + ", "
                        + rows.getLast().shown(rendering.names().nameOf(rows.getLast().source()))
                        + " name no case"),
                human);
    }

    /**
     * Every case is specified, and the row naming {@code Hit} does not hold. Whether {@code Hit} was
     * verified is then the helper's row's to say, and it held — so the measure is short of it, and
     * a count asked only of the specified cases would call it complete.
     */
    @Test
    void aCaseVerifiedOnlyByTheUnreadRowIsUndecided() {
        // The row expecting 4 is written not to hold, and that is the one refusal.
        AdequacyReport report = WrittenWitness.refusedOnly(List.of("E1905"), model(
                A_HIT_BY_A_HELPER + "    | \"a hit of three\" : (0, Hit(3)) -> 4\n" + A_MISS));
        InputCaseEvidence shot = theShot(report);

        assertEquals(shot.coverable(), List.copyOf(shot.seen().specified()),
                "every case is specified");
        assertTrue(!shot.seen().verified().containsAll(shot.coverable()),
                () -> "and one is not verified by a row that was read: " + shot.seen());
        Measurement.Partial<?> partial = assertInstanceOf(Measurement.Partial.class, shot.cases());
        assertEquals(List.of(new Weakening.InputCasesUnreadable("record", 1,
                        Set.of(aHit(report)))),
                List.copyOf(partial.weakening().causes()));
    }

    /**
     * The same, with the helper's row not holding either. It was applied and did not hold, so its
     * case is in the specified and executed sets and not in the verified one: reading it would add
     * nothing to the sets that lack a case, and the measure is exact without it.
     */
    @Test
    void anUnreadRowThatDidNotHoldLeavesNoVerifiedCaseUndecided() {
        AdequacyReport report = WrittenWitness.refusedOnly(List.of("E1905", "E1905"), model(
                "    | \"a hit\" : (0, hit(0)) -> 1\n"
                        + "    | \"a hit of three\" : (0, Hit(3)) -> 4\n" + A_MISS));
        InputCaseEvidence shot = theShot(report);

        assertEquals(1, shot.seen().unclassifiedRows(), "the helper's row is not read");
        assertEquals(shot.coverable(), List.copyOf(shot.seen().executed()),
                "every case was applied");
        assertTrue(!shot.seen().verified().containsAll(shot.coverable()),
                () -> "and one is verified by no row: " + shot.seen());
        assertInstanceOf(Measurement.Complete.class, shot.cases(),
                () -> "a row that did not hold verifies nothing, and it says " + shot.cases());
    }

    /**
     * A case the position's rules refuse is no case a row is owed at, so a set lacking only that
     * one lacks nothing a helper's row could be at.
     */
    @Test
    void aCaseTheRulesRefuseIsNotOneAnUnreadRowMayCover() {
        AdequacyReport report = WrittenWitness.reportOf("""
                module m

                data On
                data Off
                data Pending
                data Flag = On | Off | Pending
                data Active = Flag invariant value /= Off
                data Answer = Int

                behavior pick : (f: Active) -> Answer
                    constructs Answer

                let pick (f) = match f.value with
                    | On      -> Answer(1)
                    | Pending -> Answer(0)
                    | Off     -> unreachable "an Active is never Off"

                let pending (n: Int): Active = if n > 0 then Active(Pending) else Active(On)

                example pick
                    | "on" : (Active(On)) -> Answer(1)
                    | "pending" : (Active(Pending)) -> Answer(0)
                    | "pending by a helper" : (pending(1)) -> Answer(0)
                """);
        InputCaseEvidence f = report.modules().getFirst().behaviors().getFirst().signature()
                .inputs().made().orElseThrow().getFirst();

        assertEquals(1, f.excluded().size(), "Off is refused by the rules");
        assertEquals(1, f.seen().unclassifiedRows(), "the helper's row is not read");
        assertEquals(List.of(), f.unspecified(), "every case a row can be at has one");
        assertInstanceOf(Measurement.Complete.class, f.cases(),
                () -> "only the refused case is without a row, and it says " + f.cases());
    }

    /**
     * A row that did not finish while its input was being built joined none of the sets, and not
     * because of anything the model says: had it finished it may have been the row at {@code Hit}.
     * So it holds {@code Hit} undecided as a row that finished and was not read does.
     */
    @Test
    void aRowThatDidNotFinishBuildingItsInputMayBeTheRowAtAnyCase() {
        String spinning = """
                partial let spin (n: Int) : Int = if n < 0 then 0 else spin(n + 1)

                partial let spun (n: Int): Shot = Hit(spin(n))

                """;
        AdequacyReport report = WrittenWitness.refusedOnly(List.of("E1910"),
                model("    | \"spins\" : (0, spun(1)) -> 0\n" + A_MISS)
                        .replace("example record", spinning + "example record"));
        InputCaseEvidence shot = theShot(report);

        assertEquals(1, shot.unspecified().size(),
                () -> "Hit and nothing else is without a row: " + shot.unspecified());
        Measurement.Partial<?> partial = assertInstanceOf(Measurement.Partial.class, shot.cases(),
                () -> "a row that may be at Hit did not finish: " + shot.cases());
        assertEquals(List.of(new Weakening.InputCasesUnreadable("record", 1,
                        Set.of(theRow(report, "spins")))),
                List.copyOf(partial.weakening().causes()));
    }

    /**
     * Which rows a fact names is the fact, and not the order they came in: the same rows gathered
     * the other way round are the same thing a measure went without, and a set of those holds it
     * once.
     */
    @Test
    void theSameRowsInAnotherOrderAreTheSameFact() {
        RowRef one = new RowRef("record", new SourceId("m.sou"), new RowIdentity.Unnamed(1));
        RowRef two = new RowRef("record", new SourceId("m.sou"), new RowIdentity.Unnamed(2));
        Weakening forwards = new Weakening.InputCasesUnreadable("record", 1,
                new LinkedHashSet<>(List.of(one, two)));
        Weakening backwards = new Weakening.InputCasesUnreadable("record", 1,
                new LinkedHashSet<>(List.of(two, one)));

        assertEquals(forwards, backwards);
        assertEquals(1, WeakeningSet.of(forwards).union(WeakeningSet.of(backwards)).causes()
                .size());
        assertEquals(new Weakening.OutputCasesUnreadable("record",
                        new LinkedHashSet<>(List.of(one, two))),
                new Weakening.OutputCasesUnreadable("record",
                        new LinkedHashSet<>(List.of(two, one))));
    }

    /** The output side asks the same of the case a row expects. A helper's answer there is read
     *  through its value, so what leaves it unread is a row that stopped before its expectation
     *  was built. */
    private static String outputModel(String rows) {
        return """
                module m

                data Kept = Int
                data Dropped
                data Outcome = Kept | Dropped

                behavior sort : (n: Int) -> Outcome

                let sort (n) = if n >= 0 then Kept(n) else Dropped

                partial let spin (n: Int) : Int = if n < 0 then 0 else spin(n + 1)

                example sort
                """ + rows;
    }

    private static final String DROPPED = "    | \"dropped\" : (-1) -> Dropped\n";

    /** Its input never finishes, so its expectation is never read. */
    private static final String SPINS = "    | \"spins\" : (spin(1)) -> Kept(0)\n";

    private static OutputCaseEvidence theOutcome(AdequacyReport report) {
        return report.modules().getFirst().behaviors().getFirst().signature().output();
    }

    /**
     * A row whose answer is owed expects nothing (example-answer-owed). It is no row that may
     * expect {@code Kept}, so a measure beside it is exact, and {@code Kept} is missing rather
     * than undecided.
     */
    @Test
    void aRowWhoseAnswerIsOwedLeavesNoOutputCaseUndecided() {
        AdequacyReport report = WrittenWitness.reportOf(outputModel(
                "    | \"owed\" : (3) -> <?>\n" + DROPPED));
        OutputCaseEvidence outcome = theOutcome(report);

        assertEquals(0, outcome.seen().unclassifiedRows(), "the owed row expects no case");
        assertInstanceOf(Measurement.Complete.class, outcome.cases(),
                () -> "nothing here may expect Kept, and it says " + outcome.cases());
        assertEquals(List.of("Kept"), outcome.unspecified().stream().map(TypeSymbol::name)
                .toList());
    }

    /** A row that states an expectation nothing read may be the one at {@code Kept}, until a row
     *  that is read expects it. */
    @Test
    void anOutputCaseLeftToARowWhoseExpectationWasNotReadIsUndecidedAndOtherwiseItIsNot() {
        AdequacyReport named = WrittenWitness.refusedOnly(List.of("E1910"),
                outputModel(SPINS + "    | \"kept\" : (0) -> Kept(0)\n" + DROPPED));
        assertEquals(1, theOutcome(named).seen().unclassifiedRows(),
                "the row that spins was not read");
        assertInstanceOf(Measurement.Complete.class, theOutcome(named).cases(),
                () -> "every case is expected by a row, and it says " + theOutcome(named).cases());

        AdequacyReport left = WrittenWitness.refusedOnly(List.of("E1910"),
                outputModel(SPINS + DROPPED));
        Measurement.Partial<?> partial = assertInstanceOf(Measurement.Partial.class,
                theOutcome(left).cases());
        assertEquals(List.of(new Weakening.OutputCasesUnreadable("sort",
                        Set.of(theRow(left, "spins")))),
                List.copyOf(partial.weakening().causes()));
    }
}
