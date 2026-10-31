package souther.compiler.report;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.RowIdentity;
import souther.compiler.observe.RowRef;
import souther.compiler.observe.RunSensitivity;
import souther.compiler.observe.Target;
import souther.compiler.query.Adequacy;
import souther.compiler.query.InputCaseEvidence;
import souther.compiler.query.Measurement;
import souther.compiler.query.OutputCaseEvidence;
import souther.compiler.query.UnreadCase;
import souther.compiler.query.Weakening;
import souther.compiler.query.WeakeningSet;
import souther.compiler.source.SourceId;
import souther.compiler.types.TypeSymbol;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
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
        return model("", rows);
    }

    /** The same, with more declarations beside the helper. */
    private static String model(String declarations, String rows) {
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

                """ + declarations + """
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
        assertTrue(human.contains("input #2 of record — rows with a case this cannot read: "
                        + rows.getFirst().shown(rendering.names().nameOf(rows.getFirst().source()))
                        + ", "
                        + rows.getLast().shown(rendering.names().nameOf(rows.getLast().source()))
                        + ";"),
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
     * What stopped the row, as it is written where the row stopped: the one fact a measure short
     * of that row goes without, whichever measure it is.
     */
    private static Weakening.ObservationIncomplete stopOf(Measurement.Partial<?> partial,
                                                          RowRef row) {
        List<Weakening.ObservationIncomplete> stops = partial.weakening().causes().stream()
                .filter(Weakening.ObservationIncomplete.class::isInstance)
                .map(Weakening.ObservationIncomplete.class::cast)
                .filter(each -> each.met().fact().target().equals(new Target.OfRow(row)))
                .toList();
        assertEquals(1, stops.size(), () -> "the row's stop, once: " + partial.weakening());
        return stops.getFirst();
    }

    /**
     * A row that did not finish while its input was being built joined none of the sets, and not
     * because of anything its text says: had it finished it may have been the row at
     * {@code Hit}. So it holds {@code Hit} undecided — by what stopped it, which a run that allows
     * more may get past, and not as a row whose text names no case, which no run reads.
     */
    @Test
    void aRowThatDidNotFinishBuildingItsInputMayBeTheRowAtAnyCase() {
        String spinning = """
                partial let spin (n: Int) : Int = if n < 0 then 0 else spin(n + 1)

                partial let spun (n: Int): Shot = Hit(spin(n))

                """;
        AdequacyReport report = WrittenWitness.refusedOnly(List.of("E1910"),
                model(spinning, "    | \"spins\" : (0, spun(1)) -> 0\n" + A_MISS));
        InputCaseEvidence shot = theShot(report);

        assertEquals(1, shot.unspecified().size(),
                () -> "Hit and nothing else is without a row: " + shot.unspecified());
        Measurement.Partial<?> partial = assertInstanceOf(Measurement.Partial.class, shot.cases(),
                () -> "a row that may be at Hit did not finish: " + shot.cases());
        Weakening.ObservationIncomplete stop = stopOf(partial, theRow(report, "spins"));
        assertEquals(RunSensitivity.MAY_CHANGE, stop.runSensitivity());
        assertFalse(stop.figures().isEmpty(), "the figure a run would have to be allowed past");
        assertTrue(partial.weakening().causes().stream()
                        .noneMatch(Weakening.InputCasesUnreadable.class::isInstance),
                "the text of the row is not what is unread");
    }

    /**
     * The stop is one entry among what keeps the verdict open however many measures are short of the
     * row, and a reader of it is sent to what stopped the row and not to the text of its case.
     */
    @Test
    void aStoppedRowIsOneEntryAndSendsAReaderToWhatStoppedIt() {
        AdequacyReport report = WrittenWitness.refusedOnly(List.of("E1910"),
                outputModel(SPINS + DROPPED));
        RowRef spins = theRow(report, "spins");

        List<AdequacyUncertainty> aboutTheRow = report.whatKeepsTheVerdictOpen().stream()
                .filter(each -> each.subject().equals(new Subject.OfARow(spins)))
                .toList();
        assertEquals(1, aboutTheRow.size(), () -> report.whatKeepsTheVerdictOpen().toString());
        assertInstanceOf(ReaderDisposition.StoppedAtAFigure.class,
                ReaderDisposition.of(aboutTheRow.getFirst()));
        assertTrue(report.whatKeepsTheVerdictOpen().stream().noneMatch(each ->
                        ReaderDisposition.of(each) instanceof ReaderDisposition.WriteTheCaseOutIn),
                "no case is to be written out in a row that stopped");
    }

    /**
     * Rows of both reasons at once: the stop is the stop and the text is the text, each its own
     * fact, and two measures met by one stop are one stop.
     */
    @Test
    void rowsOfBothReasonsAreTwoKindsOfFact() {
        AdequacyReport report = WrittenWitness.refusedOnly(List.of("E1910"),
                outputModel(SPINS + DROPPED));
        RowRef spins = theRow(report, "spins");
        RowRef dropped = theRow(report, "dropped");
        Incompleteness.Met stop = report.modules().getFirst().behaviors().getFirst().reading()
                .gaps().stream()
                .filter(each -> each.fact().target().equals(new Target.OfRow(spins)))
                .findFirst().orElseThrow();

        WeakeningSet by = UnreadCase.weakeningOf(
                List.of(new UnreadCase.NoCaseRead(dropped),
                        new UnreadCase.Stopped(spins, List.of(stop))),
                rows -> new Weakening.OutputCasesUnreadable("sort", rows));

        assertEquals(2, by.causes().size());
        assertEquals(by, by.union(WeakeningSet.of(new Weakening.ObservationIncomplete(stop))),
                "the same stop met by another measure is the same fact");
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
        Weakening.ObservationIncomplete stop = stopOf(partial, theRow(left, "spins"));
        assertEquals(RunSensitivity.MAY_CHANGE, stop.runSensitivity(),
                "it is the row's step limit that stopped it, and a run allowed more is past it");
        assertTrue(partial.weakening().causes().stream()
                        .noneMatch(Weakening.OutputCasesUnreadable.class::isInstance),
                "the text of the row is not what is unread");
    }
}
