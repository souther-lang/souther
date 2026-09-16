package souther.compiler.query;

import souther.compiler.ast.Hir;
import souther.compiler.check.CheckSurface;
import souther.compiler.check.Sig;
import souther.compiler.inputs.InputDomain;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A point the rules cannot prove is writable, read with and without a value composed at it.
 *
 * <p>Composing settles what the rules leave open, and only there. A line drawn on a position the
 * projection reaches is proven whether or not anything was built, so a model written that way
 * answers alike both ways and can say nothing about composing — which is why the second model here
 * is read as well as the first.
 *
 * <p>What makes the first one unprovable is the field beside the one the line is on. A row at the
 * line has to be a whole record, the name that record carries is admitted by a pattern rather than
 * by a range, and the projection has no value of it to offer; the decoder does, because it builds
 * one and runs it.
 *
 * <p>Read at the reading rather than through a report. What a person is finally offered goes through
 * a composition and a settlement afterwards, and either of those can drop a row for reasons of its
 * own — so a test that read the block could not say which of the three decided it.
 */
class WhatOnlyAComposedValueShowsIsUnknownWhereNothingComposedOneTest {

    /** The line on {@code count}, reached through a record whose {@code name} no range admits. */
    private static final String INSIDE_A_RECORD = """
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

    /** The same line on the same rule, taken as the behavior's own input. */
    private static final String TAKEN_DIRECTLY = """
            module example.composeonly

            data Count = Int
                invariant value >= 1

            data Ok

            behavior f : (c: Count) -> Ok

            let f (c) = Ok

            example f
                | "away from the line" : (Count(7)) -> Ok
            """;

    @Test
    void aPointTheRulesLeaveOpenIsSettledByTheValueAndByNothingElse() {
        ObligationAssessment unread =
                theMissedPoint(INSIDE_A_RECORD, HowALineIsRead.THE_RULES_ALONE);
        assertEquals(ItemAssessment.WritabilityProjection.UNPROVEN, unread.projection(),
                "the rules do not reach the point, so nothing but a value can show it");
        assertFalse(unread.writabilityEvidence().known(),
                "and nothing composed one, so whether a row can be written here is unknown");
        assertTrue(dispositionSays(unread,
                        ObligationDisposition.Uncertainty.WhetherARowCanBeWritten.NothingShowedIt.class),
                "which the account says as the showing not having happened: " + unread.disposition());

        ObligationAssessment composed =
                theMissedPoint(INSIDE_A_RECORD, HowALineIsRead.VALUES_COMPOSED);
        assertTrue(composed.writabilityEvidence()
                        .has(ItemAssessment.WritabilityEvidence.Ground.A_VALUE_WAS_BUILT),
                "a value at the point went through this module's decoders");
        assertInstanceOf(ObligationDisposition.Unmet.class, composed.disposition(),
                "so the point is a row this model is owed rather than one nothing could say about");
    }

    /**
     * And a model whose rules reach the point cannot tell the two readings apart.
     *
     * <p>The control. Every ground the first model gains by composing is one it had nowhere else,
     * and a reader shown only that could not tell a test that watches composing from one that
     * watches the reading beside it. Here the projection proves the point, so both readings say the
     * same thing and the assertion above would hold of a build that composed nothing.
     */
    @Test
    void aPointTheRulesProveAnswersAlikeWhetherOrNotAValueWasComposed() {
        ObligationAssessment unread =
                theMissedPoint(TAKEN_DIRECTLY, HowALineIsRead.THE_RULES_ALONE);
        ObligationAssessment composed =
                theMissedPoint(TAKEN_DIRECTLY, HowALineIsRead.VALUES_COMPOSED);
        assertEquals(ItemAssessment.WritabilityProjection.PROVEN, unread.projection(),
                "the rules reach this point");
        assertTrue(unread.writabilityEvidence().known(),
                "so it is known writable with nothing composed");
        assertEquals(unread.disposition(), composed.disposition(),
                "and composing a value tells the account nothing it did not have");
    }

    private static boolean dispositionSays(ObligationAssessment owed,
                                           Class<? extends ObligationDisposition.Uncertainty> why) {
        return owed.disposition() instanceof ObligationDisposition.Undecided(var because)
                && because.written().stream().anyMatch(why::isInstance);
    }

    /**
     * The one point of the model the rows were read against and missed.
     *
     * <p>Named by what the reading came to rather than by where it is. The two models draw their
     * line on the same rule and reach it differently, so a point named by its place would be two
     * names for one question — and a row sits at the other point of each, which is what tells them
     * apart.
     */
    private static ObligationAssessment theMissedPoint(String source, HowALineIsRead reading) {
        List<BorderObligationPointAssessment> missed = new ArrayList<>();
        for (BorderObligationPointAssessment point : pointsOf(source, reading)) {
            if (point.owed().coverage() instanceof ObligationCoverage.Missed) {
                missed.add(point);
            }
        }
        assertEquals(1, missed.size(),
                () -> "the model under test has one point the rows missed: " + missed);
        return missed.get(0).owed();
    }

    private static List<BorderObligationPointAssessment> pointsOf(String source,
                                                                  HowALineIsRead reading) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Db db = compilation.db();
        String module = "example.composeonly";
        Answer<CheckSurface> prepared = db.ask(new Shapes.CheckSurface(module));
        Answer<Map<String, Sig>> sigs = db.ask(new Bodies.Signatures(module));
        assertTrue(prepared.present() && sigs.present(), "the model under test compiles");
        Map<String, InputDomain> readInputs = db.ask(new Adequacy.Inputs(module)).value();
        List<BorderAssessment> readings = new ArrayList<>();
        for (Hir.BehaviorDef behavior : prepared.value().behaviors()) {
            readings.addAll(Adequacy
                    .linesReadIn(db, module, behavior, sigs.value(), readInputs, reading)
                    .made().orElseGet(List::of));
        }
        return BorderObligationPointAssessment.across(readings);
    }
}
