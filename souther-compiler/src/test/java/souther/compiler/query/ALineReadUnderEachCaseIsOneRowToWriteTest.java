package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.BorderObligationPoint;
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
                    () -> "read under each case: " + each.said());
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
                BorderObligationPointAssessment.across(readings, point -> "the line");
        Map<String, List<BorderAssessment>> reversed = new LinkedHashMap<>();
        readings.forEach((behavior, lines) -> {
            List<BorderAssessment> back = new ArrayList<>(lines);
            java.util.Collections.reverse(back);
            reversed.put(behavior, back);
        });
        List<BorderObligationPointAssessment> backwards =
                BorderObligationPointAssessment.across(reversed, point -> "the line");

        assertEquals(points(forwards), points(backwards),
                "the same points, whichever order their readings were met in");
        for (BorderObligationPointAssessment each : forwards) {
            BorderObligationPointAssessment also = backwards.stream()
                    .filter(one -> one.point().equals(each.point())).findFirst().orElseThrow();
            assertEquals(each.met().keySet(), also.met().keySet(),
                    () -> "and every reading of each of them: " + each.said());
            assertEquals(each.owed().hasRowWitness(), also.owed().hasRowWitness(),
                    () -> "and what each came to: " + each.said());
        }
    }

    private static List<BorderObligationPoint> points(List<BorderObligationPointAssessment> each) {
        return each.stream().map(BorderObligationPointAssessment::point)
                .sorted(java.util.Comparator.comparing(Object::toString)).toList();
    }

    private static List<String> said(List<BorderObligationPointAssessment> each) {
        return each.stream().map(BorderObligationPointAssessment::said).toList();
    }

    /** The points the guard's own line is owed a row at, which are the ones a body owes. */
    private static List<BorderObligationPointAssessment> theGuardsPoints(String rows) {
        List<BorderObligationPointAssessment> points =
                compiled(rows).db().ask(new Adequacy.Obligations("example.line")).value();
        assertNotNull(points, "the model under test compiles");
        return points.stream().filter(BorderObligationPointAssessment::owedToTheReading).toList();
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
