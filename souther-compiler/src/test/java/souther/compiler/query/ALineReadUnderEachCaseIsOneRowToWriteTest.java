package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.BorderObligationPoint;
import souther.compiler.partition.GenerationOutcome;
import souther.compiler.partition.PointRole;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A guard on a name the cases of a sum spread is one row to write, read once under each case.
 *
 * <p>The name is readable at every value of the sum and a row is written under one case, so the line
 * is read as many times as there are cases and every one of those readings asks the same of a row.
 * What is owed is the line's; where it was met is the reading's.
 *
 * <p>So the readings are gathered under the point they are readings of, and a row standing at one of
 * them is the point answered. Counted per reading instead, one guard would be as many rows to write
 * as the sum has cases, and the offer for it — one row, since the point is one — would leave the
 * rest of them permanently unanswered.
 */
class ALineReadUnderEachCaseIsOneRowToWriteTest {

    /** Both cases spread {@code deadline}, and the guard names it without naming a case. */
    private static final String SPREAD = """
            module example.line

            data Base = { deadline: Int }
            data P = { ...Base, x: Int }
            data T = { ...Base, y: Int }
            data Req = P | T

            data Ok
            data No

            behavior check : (r: Req) -> Ok | No

            let check (r) = {
                guard r.deadline > 10 else No
                Ok
            }
            ROWS
            """;

    /** The rows a row written under one case gives the model. */
    private static final String UNDER_P = """

            example check
                | "on"  : (P { deadline = 11, x = 0 }) -> Ok
                | "off" : (P { deadline = 10, x = 0 }) -> No
            """;

    /** One line, one point per role, and a reading of it under each case. */
    @Test
    void oneGuardIsOnePointHoweverManyCasesReadIt() {
        List<BorderObligationPointAssessment> guarded = theGuardsPoints("");

        assertEquals(List.of(PointRole.ON, PointRole.OFF, PointRole.IN, PointRole.OUT),
                guarded.stream().map(BorderObligationPointAssessment::role).toList(),
                () -> "the four points of one line: " + said(guarded));
        for (BorderObligationPointAssessment each : guarded) {
            assertEquals(List.of("check/r@P.deadline", "check/r@T.deadline"),
                    each.met().keySet().stream().map(Object::toString).toList(),
                    () -> "read under each case: " + each.point());
        }
    }

    /**
     * A row written under one case answers the point, and the other case is still where nothing
     * stands.
     *
     * <p>Two different questions with two different answers, and the reason the readings are kept
     * beside the point rather than folded away: what is left to write is the point's answer, and
     * which case a row was actually written under is the reading's.
     */
    @Test
    void aRowUnderOneCaseAnswersThePointAndTheOtherReadingSaysNothingStandsThere() {
        BorderObligationPointAssessment on = theGuardsPoints(UNDER_P).stream()
                .filter(each -> each.role() == PointRole.ON).findFirst().orElseThrow();

        assertTrue(on.owed().hasRowWitness(), () -> "the point is answered: " + on.owed());
        assertFalse(on.owed().worthSearching(),
                () -> "so nothing is looked for at it: " + on.owed());
        Map<String, Boolean> byReading = new LinkedHashMap<>();
        on.met().forEach((where, at) ->
                byReading.put(where.toString(), at.owedAt(PointRole.ON).hasRowWitness()));
        assertEquals(Map.of("check/r@P.deadline", true, "check/r@T.deadline", false), byReading,
                () -> "and which case a row stands under is still said: " + byReading);
    }

    /**
     * Which order the readings arrive in decides nothing.
     *
     * <p>The rule a representative breaks. A point gathered from its readings is the same point
     * whichever of them the walk met first, so a search of it and what it is owed cannot turn on the
     * order — which is what a map keyed on the point and written into once per reading cannot say.
     */
    @Test
    void theOrderTheReadingsArriveInDecidesNothing() {
        Map<String, List<BorderAssessment>> readings = readingsOf("");
        List<BorderObligationPointAssessment> forwards =
                BorderObligationPointAssessment.across(readings);
        Map<String, List<BorderAssessment>> reversed = new LinkedHashMap<>();
        readings.forEach((behavior, lines) -> {
            List<BorderAssessment> back = new ArrayList<>(lines);
            java.util.Collections.reverse(back);
            reversed.put(behavior, back);
        });
        List<BorderObligationPointAssessment> backwards =
                BorderObligationPointAssessment.across(reversed);

        assertEquals(points(forwards), points(backwards),
                "the same points, whichever order their readings were met in");
        for (BorderObligationPointAssessment each : forwards) {
            BorderObligationPointAssessment also = backwards.stream()
                    .filter(one -> one.point().equals(each.point())).findFirst().orElseThrow();
            assertEquals(each.met().keySet(), also.met().keySet(),
                    () -> "and every reading of each of them: " + each.point());
            assertEquals(each.owed().hasRowWitness(), also.owed().hasRowWitness(),
                    () -> "and what each came to: " + each.point());
        }
    }

    private static List<BorderObligationPoint> points(List<BorderObligationPointAssessment> each) {
        return each.stream().map(BorderObligationPointAssessment::point)
                .sorted(java.util.Comparator.comparing(Object::toString)).toList();
    }

    /** Which points these are, as a message names them. Their own identity and not a sentence about
     *  them: a guard's line is on nothing a declaration wrote, so there is no quantity to say it
     *  on. */
    private static List<String> said(List<BorderObligationPointAssessment> each) {
        return each.stream().map(one -> one.point().toString()).toList();
    }

    /** The points the guard's own line is owed a row at, which are the ones a body owes. */
    private static List<BorderObligationPointAssessment> theGuardsPoints(String rows) {
        List<BorderObligationPointAssessment> points =
                compiled(rows).db().ask(new Adequacy.Obligations("example.line",
                        new GenerationScope.Module())).value();
        assertNotNull(points, "the model under test compiles");
        return points.stream().filter(BorderObligationPointAssessment::owedToTheReading).toList();
    }

    /**
     * A row composed at one position is not offered as the answer at another.
     *
     * <p>The other half of the same split. A row is written in the terms of the position it was
     * composed at and named for that position's point, so a coordinate handed the row composed
     * somewhere else is shown something that does not stand at it: an author writes {@code P { … }},
     * and the {@code T} coordinate they were pointed at is exactly as uncovered as before.
     *
     * <p>Nothing throws when this is wrong, which is why it is fixed here. The line is answered
     * either way and the offer looks the same in a block.
     */
    @Test
    void theRowComposedAtOnePositionIsNotTheAnswerAtAnother() {
        Map<PointRole, GenerationOutcome> away = new LinkedHashMap<>();
        compiled(UNDER_P).db().ask(new Adequacy.Generated("example.line", "check")).value()
                .generation().forEach(each -> {
                    if (each.finding().about() instanceof About.APointOfABorder(var point)
                            && !point.role().againstTheLine()
                            && point.line().cut().left().equals("r@T.deadline")) {
                        away.put(point.role(), each.outcome());
                    }
                });

        assertEquals(Map.of(PointRole.IN, new GenerationOutcome.ObligationAlreadySettled(),
                        PointRole.OUT, new GenerationOutcome.ObligationAlreadySettled()),
                away,
                () -> "the row for these was composed under the other case, so it is not what"
                        + " stands here: " + away);
    }

    /**
     * A coordinate the row was not written under is a finding, and no second row is offered for it.
     *
     * <p>The two questions coming apart. A finding stands at a coordinate — {@code T}'s side of the
     * guard has no row at it — and a row is owed once for the line, which the row under {@code P}
     * answered. Both are true at once, so an offering that took the finding for a claim about the
     * line would refuse to run, and one that took the line's answer for the finding's would write
     * {@code T} a row for work already done.
     */
    @Test
    void aCoordinateNoRowStandsAtIsNotOfferedASecondRowForTheSameLine() {
        Compilation compilation = compiled(UNDER_P);
        // Run at all, which is half of what this fixes: a request that read the finding as a claim
        // about the line met a line already answered and refused to go on.
        Offering offering = Adequacy.offeredFor(compilation.db(),
                OfferingRequest.overTheModule("example.line", true));
        assertNotNull(offering, "an offering is made for a model in this state");

        Map<PointRole, GenerationOutcome> againstTheLine = new LinkedHashMap<>();
        compilation.db().ask(new Adequacy.Generated("example.line", "check")).value()
                .generation().forEach(each -> {
                    if (each.finding().about() instanceof About.APointOfABorder(var point)
                            && point.role().againstTheLine()) {
                        againstTheLine.put(point.role(), each.outcome());
                    }
                });
        assertEquals(Map.of(PointRole.ON, new GenerationOutcome.ObligationAlreadySettled(),
                        PointRole.OFF, new GenerationOutcome.ObligationAlreadySettled()),
                againstTheLine,
                () -> "the coordinates under `T` are findings whose line is answered, and no row"
                        + " is composed a second time for them: " + againstTheLine);
    }

    private static Map<String, List<BorderAssessment>> readingsOf(String rows) {
        List<BorderAssessment> lines = compiled(rows).db()
                .ask(new Adequacy.Boundaries("example.line", "check")).value();
        assertNotNull(lines, "the model under test compiles");
        return Map.of("check", lines);
    }

    private static Compilation compiled(String rows) {
        Compilation compilation =
                Compilation.ofSource(SPREAD.replace("ROWS", rows), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
