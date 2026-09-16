package souther.compiler.query;

import souther.compiler.partition.BorderObligationPoint;
import souther.compiler.partition.FixtureTemplate;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * One request for rows, asked of two builds that measure differently, answered the same way.
 *
 * <p>What a person asking for the rows their model does not cover is handed follows from the
 * request. A build states how much of itself it wants told about, which is a budget for the report
 * beside the code and says nothing about the question this request puts — so two builds that
 * disagree about it answer this alike, and a run that read the dial would answer three callers
 * three ways for one request.
 *
 * <p>The model draws its line at a point the rules cannot reach, which is where the two readings of
 * a line part company: composing settles it and the rules alone leave it open. So this holds of a
 * model that has something for it to hold of, and what the two readings come to there is fixed
 * beside it ({@link WhatOnlyAComposedValueShowsIsUnknownWhereNothingComposedOneTest}).
 *
 * <p><b>The account and not only the rows.</b> Which rows are composed is resolved from the search
 * whatever was measured, so a run reading the dial hands over the same rows and a different account
 * of what they leave — a point this model is owed a row at, or one nothing has shown anything
 * about. Both are what the request is answered with, and a test watching the rows alone would call
 * that answered.
 *
 * <p>Nothing here forks, so what the arms of a body took is no part of this answer and the two
 * builds below are alike in every way that reaches it but the one under test.
 */
class WhatARequestIsOfferedDoesNotTurnOnWhatTheBuildMeasuresTest {

    private static final String MODULE = "example.composeonly";

    private static final String MODEL = """
            module example.composeonly

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

    @Test
    void twoBuildsMeasuringDifferentlyAreOfferedTheSameRows() {
        Compilation measuringLess = measured(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        Compilation measuringAll = measured(Adequacy.Asked.fullReport());
        readTheLinesDifferently(measuringLess, measuringAll);

        List<String> less = rowsOf(offering(measuringLess));
        assertFalse(less.isEmpty(),
                "the model under test is offered rows, so the two answers are not both empty");
        assertEquals(less, rowsOf(offering(measuringAll)),
                "and what the request is offered is the same work either way");
    }

    @Test
    void andTheSameAccountOfWhatThoseRowsLeave() {
        Compilation measuringLess = measured(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        Compilation measuringAll = measured(Adequacy.Asked.fullReport());
        readTheLinesDifferently(measuringLess, measuringAll);

        List<String> less = accountOf(offering(measuringLess));
        assertFalse(less.isEmpty(),
                "the model under test has points in the account, so the two are not both empty");
        assertEquals(less, accountOf(offering(measuringAll)),
                "and each of them stands where it stands whatever the build measured");
    }

    /**
     * That the two builds really do put different questions to the lines.
     *
     * <p>What makes the comparisons about something. Read off the compilations rather than taken
     * from the levels written above: a change that made the two levels read the lines alike would
     * otherwise leave both tests passing while comparing one thing with itself.
     */
    private static void readTheLinesDifferently(Compilation less, Compilation all) {
        assertEquals(HowALineIsRead.THE_RULES_ALONE, Adequacy.linesAskedOf(less.db()),
                "the build measuring less reads the lines from the rules");
        assertEquals(HowALineIsRead.VALUES_COMPOSED, Adequacy.linesAskedOf(all.db()),
                "and the build measuring everything composes values at them");
    }

    private static Compilation measured(Adequacy.Asked asked) {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(asked);
        compilation.answerEverything();
        return compilation;
    }

    private static Offering offering(Compilation compilation) {
        Offering offering = Adequacy.offeredFor(compilation.db(),
                OfferingRequest.overTheModule(MODULE));
        assertNotNull(offering, "the model under test compiles");
        return offering;
    }

    /**
     * The work the request is handed, as what each row is for and what it holds.
     *
     * <p>Not the {@link Offering} itself. What a search tried on the way to composing a row is kept
     * beside the rows and is a fact about the search rather than about the work offered, so an
     * answer compared whole would hold the two builds to their searches having gone the same way —
     * which is what a level is for.
     */
    private static List<String> rowsOf(Offering offering) {
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

    /** Where each point of the request's lines stands, which is the other half of the answer. */
    private static List<String> accountOf(Offering offering) {
        List<String> out = new ArrayList<>();
        for (Map.Entry<BorderObligationPoint, BorderAccount.Answer> at
                : offering.account().resolved().entrySet()) {
            ObligationAssessment owed = at.getValue().point().owed();
            out.add(at.getKey() + " | " + owed.disposition()
                    + " | " + owed.writabilityEvidence().grounds().written());
        }
        return out;
    }
}
