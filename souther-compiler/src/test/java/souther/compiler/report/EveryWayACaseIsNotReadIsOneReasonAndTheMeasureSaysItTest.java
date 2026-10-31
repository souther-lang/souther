package souther.compiler.report;

import souther.compiler.observe.RunSensitivity;
import souther.compiler.query.InputCaseEvidence;
import souther.compiler.query.Measurement;
import souther.compiler.query.OutputCaseEvidence;
import souther.compiler.query.Weakening;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every way a row's case is not read has one reason, and the measure says that reason and no other.
 *
 * <p>Which reason follows from how far the row got and what is on record about it, so the cases
 * below are the cells of that table, each written as a model a person could write: a row that
 * never had its values handed over and was stopped, one that never did and was refused, one whose
 * values were handed over and wrote no case, and one both of those at once. What the reasons are
 * is {@code UnreadCase}'s.
 *
 * <p>The row read as a case a person is to write out when it is not one is what the reviews of the
 * change that made these keep finding, one cell at a time. So the table is held here whole.
 */
class EveryWayACaseIsNotReadIsOneReasonAndTheMeasureSaysItTest {

    private static final String SPIN =
            "partial let spin (n: Int) : Int = if n < 0 then 0 else spin(n + 1)\n";

    private static String output(String rows) {
        return """
                module m

                data Kept = Int
                data Dropped
                data Outcome = Kept | Dropped

                behavior sort : (n: Int) -> Outcome

                let sort (n) = if n >= 0 then Kept(n) else Dropped

                example sort
                """ + rows;
    }

    private static String input(String hitArm, String declarations, String rows) {
        return """
                module m

                data Shot = Hit | Miss

                data Hit = Int
                    invariant value >= 0

                behavior record : (bonus: Int, shot: Shot) -> Int

                let record (bonus, shot) =
                    match shot with
                        | Hit as h -> %s
                        | Miss -> bonus

                let hit (n: Int): Shot = Hit(n)

                %s
                example record
                """.formatted(hitArm, declarations) + rows;
    }

    private static final String A_MISS = "    | \"a miss\" : (0, Miss) -> 0\n";

    private static OutputCaseEvidence theOutcome(AdequacyReport report) {
        return report.modules().getFirst().behaviors().getFirst().signature().output();
    }

    private static InputCaseEvidence theShot(AdequacyReport report) {
        return report.modules().getFirst().behaviors().getFirst().signature().inputs().made()
                .orElseThrow().get(1);
    }

    /** Asked of everything the scope has not answered, and not of what keeps the verdict open:
     *  a verdict a gap refuses is open on nothing, and the entries are there all the same. */
    private static boolean sendsAReaderToWriteACaseOut(AdequacyReport report) {
        return report.assessment().uncertainties().stream().anyMatch(each ->
                ReaderDisposition.of(each) instanceof ReaderDisposition.WriteTheCaseOutIn);
    }

    /**
     * The wrong number of inputs, with the expectation written out as {@code Kept(1)}. The row is
     * refused before its expectation is read, so it is not a row whose text names no case, and
     * there is nothing to write out in it: the refusal is reported where the row is.
     */
    @Test
    void aRowRefusedBeforeItsExpectationWasReadLeavesNoOutputCaseUndecided() {
        AdequacyReport report = WrittenWitness.refusedOnly(List.of("E1903"), output(
                "    | \"invalid\" : (1, 2) -> Kept(1)\n    | \"dropped\" : (-1) -> Dropped\n"));
        OutputCaseEvidence outcome = theOutcome(report);

        assertEquals(1, outcome.seen().unclassifiedRows(), "the row is still counted as unread");
        assertInstanceOf(Measurement.Complete.class, outcome.cases(),
                () -> "a refused row cannot be the one that expects Kept: " + outcome.cases());
        assertEquals(1, outcome.unspecified().size(), "and Kept is missing, which is known");
        assertTrue(!sendsAReaderToWriteACaseOut(report),
                () -> "no case is to be written out: " + report.assessment().uncertainties());
    }

    /** An input that breaks the invariant of its type is refused the same way at an input. */
    @Test
    void aRowRefusedAtAnInputLeavesNoInputCaseUndecided() {
        AdequacyReport report = WrittenWitness.refusedOnly(List.of("E1903"), input(
                "h.value + bonus", "",
                "    | \"hit below nought\" : (0, Hit(-1)) -> 0\n" + A_MISS));
        InputCaseEvidence shot = theShot(report);

        assertEquals(1, shot.seen().unclassifiedRows(), "the row is still counted as unread");
        assertInstanceOf(Measurement.Complete.class, shot.cases(),
                () -> "a refused row cannot be the one at Hit: " + shot.cases());
        assertEquals(1, shot.unspecified().size(), "and Hit is missing, which is known");
        assertTrue(!sendsAReaderToWriteACaseOut(report),
                () -> "no case is to be written out: " + report.assessment().uncertainties());
    }

    /**
     * Values handed over, a helper's answer at the input, and the run stopped after: the row's text
     * names no case and the run did not finish, and either alone leaves {@code Hit} undecided. Both
     * are said, the stop with its figure and the text as a row to write out, and it is one row.
     */
    @Test
    void aRowThatStoppedAfterItsValuesWereHandedOverIsBothReasons() {
        AdequacyReport report = WrittenWitness.refusedOnly(List.of("E1910"), input(
                "spin(h.value)", SPIN,
                "    | \"spins\" : (0, hit(0)) -> 0\n" + A_MISS));
        InputCaseEvidence shot = theShot(report);

        Measurement.Partial<?> partial = assertInstanceOf(Measurement.Partial.class, shot.cases(),
                () -> "Hit may be where the row would have held: " + shot.cases());
        assertEquals(1, shot.seen().unclassifiedRows(), "two reasons, one row");
        assertTrue(partial.weakening().causes().stream().anyMatch(each ->
                        each instanceof Weakening.ObservationIncomplete it
                                && it.runSensitivity() == RunSensitivity.MAY_CHANGE),
                () -> "the stop, which a wider run may get past: " + partial.weakening());
        assertTrue(partial.weakening().causes().stream()
                        .anyMatch(Weakening.InputCasesUnreadable.class::isInstance),
                () -> "and the text, which no run reads: " + partial.weakening());
    }

    /**
     * Values handed over, the case written out, and the run stopped after. The case is counted at
     * every set the row got to, and the stop is what the reading of the rows says of it once; this
     * measure is not short of the row.
     */
    @Test
    void aRowThatStoppedAfterItsCaseWasReadLeavesTheCaseCounted() {
        AdequacyReport report = WrittenWitness.refusedOnly(List.of("E1910"), input(
                "spin(h.value)", SPIN,
                "    | \"spins\" : (0, Hit(0)) -> 0\n" + A_MISS));
        InputCaseEvidence shot = theShot(report);

        assertEquals(0, shot.seen().unclassifiedRows(), "its case was read");
        assertEquals(List.of(), shot.unspecified(), "and counted");
        assertInstanceOf(Measurement.Complete.class, shot.cases(),
                () -> "nothing here is unread: " + shot.cases());
    }

    /**
     * What a model with no row stopped or refused says is what it said: the helper's row decides
     * only a case no row is counted at.
     */
    @Test
    void aRowWhoseTextNamesNoCaseIsStillTheOnlyReasonItIsReadAsWhenNothingStoppedIt() {
        AdequacyReport report = WrittenWitness.reportOf(input("h.value + bonus", "",
                "    | \"a hit\" : (0, hit(0)) -> 0\n" + A_MISS));
        InputCaseEvidence shot = theShot(report);

        Measurement.Partial<?> partial = assertInstanceOf(Measurement.Partial.class, shot.cases());
        assertEquals(1, partial.weakening().causes().size(), partial.weakening()::toString);
        Weakening only = List.copyOf(partial.weakening().causes()).getFirst();
        assertInstanceOf(Weakening.InputCasesUnreadable.class, only);
        assertEquals(RunSensitivity.UNAFFECTED, only.runSensitivity());
        assertTrue(sendsAReaderToWriteACaseOut(report), "and a reader is sent to the row");
    }
}
