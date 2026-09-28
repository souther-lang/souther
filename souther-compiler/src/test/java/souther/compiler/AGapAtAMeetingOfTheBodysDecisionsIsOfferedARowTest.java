package souther.compiler;

import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.ObligationIdentity;
import souther.compiler.query.About;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAccount;
import souther.compiler.query.Compilation;
import souther.compiler.query.Composition;
import souther.compiler.query.OfferingRequest;
import souther.compiler.query.RowKey;
import souther.compiler.query.Settlement;
import souther.compiler.query.Settlements;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A combination of the body's decisions nothing makes is raised, offered a row, and answered by it.
 *
 * <p>The way round, for the criterion the pair space is not. A behavior whose decisions meet is held
 * to those meetings, and the four rows below go through every arm and every rule of this body while
 * leaving two of its six combinations unmade — so what the author is owed is a row that makes one,
 * and a run that could not compose one would raise a gap nothing could close.
 *
 * <p>Which is the state this was in. The search already looked in the body's combinations, and it
 * looked in them on an arm's behalf: a meeting no arm was owed at was never somewhere to look, and
 * a meeting is exactly what rows through every arm can leave unmade.
 */
class AGapAtAMeetingOfTheBodysDecisionsIsOfferedARowTest {

    /** Two decisions meeting at one value: three outcomes and two, so six combinations. */
    private static final String MODEL = """
            module example.meeting

            data Total = Int
            data Premium
            data Standard
            data Membership = Premium | Standard
            data Express
            data Regular
            data Delivery = Express | Regular
            data Fee = Int

            behavior shippingFee : (total: Total, member: Membership, delivery: Delivery) -> Fee
                constructs Fee

            let shippingFee (total, member, delivery) =
                Fee(baseFee(total, member) + expressFee(delivery))

            let baseFee (total: Total, member: Membership): Int =
                match member with
                    | Premium -> 0
                    | Standard -> if total.value >= 5000 then 0 else 500

            let expressFee (delivery: Delivery): Int =
                match delivery with
                    | Express -> 500
                    | Regular -> 0

            example shippingFee
                | (Total(0), Premium, Express)     -> Fee(500)
                | (Total(0), Standard, Regular)    -> Fee(500)
                | (Total(5000), Premium, Regular)  -> Fee(0)
                | (Total(5000), Standard, Express) -> Fee(500)
            """;

    /**
     * Every arm is taken, two meetings are unmade, and each of them is offered a row.
     *
     * <p>The rows go in and the gaps go: what is offered answers what was raised, and asking again
     * offers nothing. A search that composed a row for an arm instead would leave the same
     * meetings unmade, and the second reading would raise them again.
     */
    @Test
    void aMeetingNoRowMakesIsRaisedOfferedAndThenGone() {
        Compilation before = measured(MODEL);

        assertEquals(before.db() == null ? -1 : armsOf(before).counted(), armsOf(before).covered(),
                "every arm of the body already has a row through it");
        List<String> raised = gapsOf(before);
        assertEquals(2, raised.size(), () -> "two of the six combinations are unmade: " + raised);

        String block = block(before);
        List<String> rows = rowsOf(block);
        assertFalse(rows.isEmpty(), () -> "a row is offered for them: " + block);

        Compilation after = measured(MODEL + String.join("\n", rows) + "\n");
        assertEquals(List.of(), after.errors(),
                () -> "the rows offered are rows this model admits:\n" + String.join("\n", rows));
        assertEquals(List.of(), gapsOf(after),
                () -> "and they answer the combinations: " + report(after));
        assertTrue(rowsOf(block(after)).isEmpty(),
                () -> "so nothing is offered a second time: " + block(after));
    }

    /**
     * Every arm is already covered, and each of the two meetings is requested, has a row composed
     * for it, and is settled by that row.
     *
     * <p>Not "a row is offered somewhere": which obligation asked for it and which row answers it,
     * read off the same table the offering itself reduces from. A meeting composed a row and never
     * requested would be reduced away as redundant before an author ever saw it, which is the
     * defect this pins against reappearing.
     */
    @Test
    void theSettlementsForEachMeetingHoldItsOwnRow() {
        Compilation before = measured(MODEL);

        souther.compiler.query.ArmSummary arms = armsOf(before);
        assertEquals(arms.counted(), arms.covered(), "every arm is already covered");

        Set<ObligationIdentity.OfACombinationOfDecisions> meetings = meetingsOf(before);
        assertEquals(2, meetings.size(), () -> "the two unmade combinations: " + meetings);

        Settlements table = settlementsOf(before);
        for (ObligationIdentity.OfACombinationOfDecisions meeting : meetings) {
            assertTrue(table.requested().contains(meeting),
                    () -> meeting + " is requested: " + table.requested());
            RowKey row = table.composedFor().get(meeting);
            assertNotNull(row, () -> "a row was composed for " + meeting);
            assertInstanceOf(Settlement.Settles.class, table.at(row, meeting),
                    () -> "and it settles what it was composed for: " + meeting);
        }
    }

    /**
     * The count the report writes over a gap and the marks it prints for one agree.
     *
     * <p>The two are written by different lines of the report, over the same findings — a mismatch
     * is one of them forgetting a kind the other still counts, which is what a meeting's mark going
     * unprinted looked like before it was offered one.
     */
    @Test
    void theHumanReportMarksEachMeetingGapItCounts() {
        Compilation before = measured(MODEL);
        String report = report(before);

        assertEquals(gapsMarked(report), markedGapLines(report).size(),
                () -> "the count over a strict build's gaps and the marks under them: " + report);
        assertEquals(2, markedGapLines(report).stream()
                        .filter(line -> line.contains("no row makes this combination of the"
                                + " decisions"))
                        .count(),
                () -> "one mark per meeting nothing made: " + report);
    }

    /** The number a strict build's own line says it refuses over, or -1 where it says none. */
    private static int gapsMarked(String report) {
        return report.lines()
                .filter(line -> line.endsWith("marked `!`: what a strict build refuses over."))
                .map(line -> line.strip().split(" ", 2)[0])
                .mapToInt(Integer::parseInt)
                .findFirst().orElse(-1);
    }

    /** Every line the report prints a finding under with the `!` mark a strict build refuses over. */
    private static List<String> markedGapLines(String report) {
        return report.lines().filter(line -> line.strip().startsWith("! ")).toList();
    }

    /** The combinations of this body's decisions nothing has made, as the account states them. */
    private static Set<ObligationIdentity.OfACombinationOfDecisions> meetingsOf(
            Compilation compilation) {
        Set<ObligationIdentity.OfACombinationOfDecisions> out = new java.util.LinkedHashSet<>();
        for (Adequacy.Finding each : AdequacyReport.of(compilation).adequacyGaps()) {
            if (each.about() instanceof About.ACombinationNoRowMakes(var combination)) {
                out.add(combination);
            }
        }
        return out;
    }

    /** The offering's own table of what each row would settle, built the way an offering is. */
    private static Settlements settlementsOf(Compilation compilation) {
        OfferingRequest request = OfferingRequest.overTheModule("example.meeting");
        Map<String, Adequacy.Filling> generated =
                Adequacy.generatedOf(compilation.db(), request.module());
        BorderAccount account = Adequacy.accountFor(compilation.db(), request.module(),
                request.scope());
        Composition composed = Composition.composed(request, generated, account);
        return Settlements.of(compilation.db(), composed);
    }

    /** The rows of an offered block, as a person pastes them under the example already written. */
    private static List<String> rowsOf(String block) {
        return block.lines()
                .filter(each -> each.strip().startsWith("| (Total"))
                .map(each -> "    " + each.strip())
                .toList();
    }

    private static souther.compiler.query.ArmSummary armsOf(Compilation compilation) {
        return AdequacyReport.of(compilation).modules().getFirst().behaviors().getFirst()
                .evidence().branch().arms();
    }

    /** What a strict build refuses over here, in the words the report writes. */
    private static List<String> gapsOf(Compilation compilation) {
        return AdequacyReport.of(compilation).adequacyGaps().stream()
                .filter(each -> each.kind() == Adequacy.Kind.INTERACTION_UNCOVERED)
                .map(each -> each.about().toString())
                .toList();
    }

    private static String block(Compilation compilation) {
        return GeneratedRows.of(
                Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("example.meeting")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                compilation.db()).text();
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
