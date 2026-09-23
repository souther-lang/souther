package souther.compiler.query;

import souther.compiler.partition.BorderObligationPoint;
import souther.compiler.partition.FixtureTemplate;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What one request for rows is answered with, over every level a build can measure at.
 *
 * <p>The whole of what this issue is about, said once. A build states how much of itself it wants
 * told about; a caller states which readings of a module it wants rows for. The second is a
 * question and the first is a budget for a document beside it, so a run that answered the question
 * from the budget handed three callers three answers to one request — an editor at whatever the
 * workspace is set to, a command asking for the whole report, and a compile holding neither.
 *
 * <p><b>At one observation of the rows.</b> What a compilation is able to say is settled before a
 * row runs: a run that recorded nothing has nothing to say about the arms of a body, and a build
 * that read none of its rows does not know which of them are already written. That is availability
 * and not a dial ({@link WhatTheArmsShowAnOfferingComesFromTheRunAndNotTheReportTest}), and it is
 * what a caller composing rows asks for — so every compilation below is asked for it, and is held
 * to having it before it is compared. What is left varying is how much of itself the build asked to
 * be told about, which is the thing under test.
 *
 * <p>Three models, because the readings they part company over are three different things: a line
 * the rules reach, a line only a composed value settles, and a meeting of a body's decisions that
 * no row makes. A law held over one of them says nothing about the other two.
 */
class OneRequestIsAnsweredAlikeWhateverTheBuildMeasuresTest {

    /** A line the rules reach: what is known there is known with nothing built. */
    private static final String THE_RULES_REACH_IT = """
            module example.answered

            data Count = Int
                invariant value >= 0 && value <= 10

            data Ok

            behavior f : (c: Count) -> Ok

            let f (c) = Ok

            example f
                | "away from the line" : (Count(3)) -> Ok
            """;

    /** A line only a value put through the decoders settles. */
    private static final String ONLY_A_VALUE_SHOWS_IT = """
            module example.answered

            data Name = String
                invariant String.matches("[A-Z]{1,8}", value)

            data Count = Int
                invariant value >= 1

            data Rec = { name: Name, count: Count }

            data Ok

            behavior f : (r: Rec) -> Ok

            let f (r) = Ok

            example f
                | "away from the line" : (Rec { name = Name("ACME"), count = Count(7) }) -> Ok
            """;

    /** A meeting of two decisions that rows through every arm leave unmade. */
    private static final String A_MEETING_NO_ROW_MAKES = """
            module example.answered

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

    @Test
    void aLineTheRulesReachIsAnsweredAlike() {
        alikeAtEveryLevel(THE_RULES_REACH_IT);
    }

    @Test
    void aLineOnlyAComposedValueShowsIsAnsweredAlike() {
        alikeAtEveryLevel(ONLY_A_VALUE_SHOWS_IT);
    }

    @Test
    void aMeetingNoRowMakesIsAnsweredAlike() {
        alikeAtEveryLevel(A_MEETING_NO_ROW_MAKES);
    }

    /**
     * The same request, put to a build at each level, answered the same way.
     *
     * <p>Rows and the account of what they leave, which is what a person is handed and what the
     * block says about it. Not the {@link Offering} whole: what a search tried on the way to
     * composing a row is a fact about the search, and holding the levels to their searches having
     * gone the same way is holding them to the thing a level is for.
     */
    private static void alikeAtEveryLevel(String model) {
        List<String> first = null;
        Set<HowALineIsRead> linesRead = EnumSet.noneOf(HowALineIsRead.class);
        for (Adequacy.Level level : Adequacy.Level.values()) {
            List<String> answered = answeredAt(model, level, linesRead);
            if (first == null) {
                first = answered;
                assertFalse(first.isEmpty(),
                        () -> "the model under test is answered with something, so the levels are"
                                + " not all being compared against nothing");
            } else {
                assertEquals(first, answered,
                        "a build measuring at " + level + " answers the request as the others do");
            }
        }
        // Read off the compilations rather than taken from the levels: a change that made every
        // level read the lines alike would otherwise leave this comparing one thing with itself.
        assertEquals(EnumSet.allOf(HowALineIsRead.class), linesRead,
                "the levels compared put different questions to the lines");
    }

    private static List<String> answeredAt(String model, Adequacy.Level level,
                                           Set<HowALineIsRead> linesRead) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        // What a caller composing rows needs of the run, said of every one of them. Left to the
        // level, the comparison below would be moving two things and reporting one.
        compilation.observe(RowObservation.RECORD_ARMS);
        compilation.measure(Adequacy.Asked.reportOnly(level));
        compilation.answerEverything();
        assertEquals(RowObservation.RECORD_ARMS, Adequacy.observationAsked(compilation.db()),
                "every build here reads its rows and records where they went, whatever it reports");
        linesRead.add(Adequacy.linesAskedOf(compilation.db()));

        Offering offering = Adequacy.offeredFor(compilation.db(),
                OfferingRequest.overTheModule("example.answered"));
        assertNotNull(offering, "the model under test compiles");
        List<String> out = new ArrayList<>();
        offering.rowsByBehavior().forEach((behavior, rows) -> {
            for (OfferedRow row : rows) {
                out.add("row " + behavior + " | " + row.key()
                        + " | " + row.inputs().stream().map(FixtureTemplate::text).toList()
                        + " | " + row.namedFor());
            }
        });
        for (Map.Entry<BorderObligationPoint, BorderAccount.Answer> at
                : offering.account().resolved().entrySet()) {
            ObligationAssessment owed = at.getValue().point().owed();
            out.add("point " + at.getKey() + " | " + owed.disposition()
                    + " | " + owed.writabilityEvidence().grounds().written());
        }
        return out;
    }
}
