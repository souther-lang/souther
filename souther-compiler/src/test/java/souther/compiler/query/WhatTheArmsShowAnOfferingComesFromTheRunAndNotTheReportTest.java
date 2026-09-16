package souther.compiler.query;

import souther.compiler.observe.ArmObservation;
import souther.compiler.partition.FixtureTemplate;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What the arms of a body show an offering comes from the run, and not from what was reported.
 *
 * <p>A meeting of two decisions that no row makes is a row this model is owed, and finding out
 * which meetings the rows made takes the classes having recorded where each row went. That is the
 * compilation's own arrangement, settled before a row runs and held to by everything that reads
 * one — so a caller asking for rows says it needs the recording, and what it is then offered is the
 * same whatever the build asked to be told about.
 *
 * <p>Beside the level-independence of the lines rather than inside it
 * ({@link WhatARequestIsOfferedDoesNotTurnOnWhatTheBuildMeasuresTest}). Which lines a request is
 * answered at follows from the request; what the arms show is available or not, and a compilation
 * whose rows recorded nothing has nothing to say about them. So what is held here is that the
 * report's dial does not decide it, and the control below is that the recording does.
 */
class WhatTheArmsShowAnOfferingComesFromTheRunAndNotTheReportTest {

    private static final String MODULE = "example.meeting";

    /** Two decisions meeting at one value: rows through every arm leave two meetings unmade. */
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
     * One request, two builds recording the arms and measuring differently, offered the same rows.
     *
     * <p>The narrower build reports nothing about the arms and records them all the same, because
     * something reaching it asked for the rows. What it is offered is what the wider one is.
     */
    @Test
    void aBuildThatRecordsTheArmsIsOfferedTheSameRowsWhateverItReports() {
        List<String> reportingLess = rowsOffered(
                Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS), ArmObservation.RECORD);
        assertFalse(reportingLess.isEmpty(),
                "the model leaves meetings unmade, so rows are offered for them");
        assertEquals(reportingLess,
                rowsOffered(Adequacy.Asked.fullReport(), ArmObservation.RECORD),
                "and the build that reports everything is offered the same ones");
    }

    /**
     * And a build whose rows recorded nothing has nothing to offer for them.
     *
     * <p>The control, and the reason the sentence above is about the recording rather than about
     * nothing. Which meetings the rows made is read off what the rows recorded, so a run that
     * recorded nothing leaves the account unable to say a meeting was missed — which is what makes
     * asking for the recording part of asking for the rows rather than a dial beside it.
     */
    @Test
    void andOneThatRecordedNothingIsOfferedNoneOfThem() {
        assertNotEquals(
                rowsOffered(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS),
                        ArmObservation.RECORD),
                rowsOffered(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS),
                        ArmObservation.OMIT),
                "what the arms show is available because the run recorded it");
    }

    private static List<String> rowsOffered(Adequacy.Asked asked, ArmObservation arms) {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.observe(arms == ArmObservation.RECORD
                ? RowObservation.RECORD_ARMS : RowObservation.READ);
        compilation.measure(asked);
        compilation.answerEverything();
        Offering offering = Adequacy.offeredFor(compilation.db(),
                OfferingRequest.overTheModule(MODULE));
        assertNotNull(offering, "the model under test compiles");
        List<String> out = new ArrayList<>();
        offering.rowsByBehavior().forEach((behavior, rows) -> {
            for (OfferedRow row : rows) {
                out.add(behavior + " | " + row.key()
                        + " | " + row.inputs().stream().map(FixtureTemplate::text).toList()
                        + " | " + row.namedFor());
            }
        });
        return out;
    }
}
