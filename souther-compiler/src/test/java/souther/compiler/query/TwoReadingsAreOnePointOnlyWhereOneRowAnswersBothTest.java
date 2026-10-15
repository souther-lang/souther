package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleRef;
import souther.compiler.numeric.Towards;
import souther.compiler.partition.Demand;
import souther.compiler.partition.PointRole;
import souther.compiler.types.WrittenOwner;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison a body wrote owes the points of the line its author wrote, and each reading asks for
 * them in its own terms.
 *
 * <p>The guard below is one line and four points however many cases it is read under. Where a
 * region beside it stops is the reading's: under {@code P} the run above the line stops at 20 and
 * under {@code T} at 30, which a declaration put there and the guard did not. So the far end is
 * part of what a reading asks for at the point and no part of which point it is, and a row in
 * either run is a row in the author's region — counted for the reading it was written under, and
 * for that one alone.
 *
 * <p>A line a declaration drew is the other way round: its far end is where the type stops it and
 * the same at every reading, and two far ends there are two points
 * ({@link souther.compiler.partition.RegionBasis}).
 */
class TwoReadingsAreOnePointOnlyWhereOneRowAnswersBothTest {

    /** One guard on a spread name, and a far side that differs by case. */
    private static final String CAPPED_APART = """
            module example.line

            data Base = { deadline: Int }
            data P = { ...Base, x: Int }
                invariant capP = deadline <= 20
            data T = { ...Base, y: Int }
                invariant capT = deadline <= 30
            data Req = P | T

            data Ok
            data No

            behavior check : (r: Req) -> Ok | No

            let check (r) = {
                guard r.deadline > 10 else No
                Ok
            }
            """;

    /** One point in each of the four, the run above the line too, though it stops in two places. */
    @Test
    void aRegionStoppedInTwoPlacesIsOnePointOfTheAuthorsLine() {
        Map<PointRole, List<BorderObligationPointAssessment>> byRole = theGuardsPoints();

        for (PointRole role : PointRole.values()) {
            assertEquals(1, byRole.get(role).size(),
                    () -> "the author wrote one line, which owes one " + role + " point: "
                            + byRole.get(role));
        }
    }

    /**
     * And every point is read under each case, the run above the line asked for as each case
     * stops it.
     */
    @Test
    void aPointIsReadUnderEveryCaseAndAskedForAsThatCaseStopsIt() {
        Map<PointRole, List<BorderObligationPointAssessment>> byRole = theGuardsPoints();

        for (PointRole role : PointRole.values()) {
            assertEquals(List.of("r@P.deadline", "r@T.deadline"),
                    readings(byRole.get(role).get(0)),
                    () -> "the " + role + " point is read under each case");
        }
        BorderObligationPointAssessment above = byRole.get(PointRole.IN).get(0);
        List<Demand> asked = above.readings().stream()
                .map(each -> each.border().demand(above.askedAt(each))).toList();
        assertFalse(asked.get(0).sameAs(asked.get(1)),
                () -> "a run that stops at 20 and one that stops at 30 ask for different rows: "
                        + asked);
    }

    /**
     * A reading offered twice is refused rather than counted twice.
     *
     * <p>What a search of one of them came to would stand for the other, chosen by the order the
     * walk took — so two readings this cannot tell apart are not two readings, and saying so is the
     * only answer that does not depend on which arrived first. What it says is about the caller:
     * these are lines already folded on where each was read, so one line at one place twice is a
     * list that was never merged.
     */
    @Test
    void aReadingOfferedTwiceIsRefused() {
        List<BorderAssessment> lines = boundaries();
        List<BorderAssessment> twice = new ArrayList<>(lines);
        twice.addAll(lines);

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> BorderObligationPointAssessment.across(twice, _ -> List.of()));
        assertTrue(refused.getMessage().contains("never merged"), refused::getMessage);
    }

    /**
     * Two calls putting one comparison at one place facing its author's sides two ways are two
     * readings, and what a row showed is counted for the author's point it is at in each.
     *
     * <p>{@code check(a, 10)} holds up to ten on {@code a} and {@code check(20 - a, 10)} from ten
     * up, and both are evaluated on every row. The value beside the author's line on the side where
     * {@code x <= limit} fails is eleven on {@code a} for the first call and nine for the second,
     * and the run past it is above eleven for the first and below nine for the second. The rows at
     * eight and nine are rows at the second call's places of those two points and at neither of
     * the first's; merged as one reading of one place, they were counted for the first call's points
     * or not at all.
     *
     * <p>The run on the holding side is asked of neither call here: each call's line stops the
     * other's run at ten, which is the value at the line.
     */
    @Test
    void aCallTurningTheQuantityRoundAtOnePlaceIsAReadingOfItsOwn() {
        List<BorderObligationPointAssessment> points = pointsOf("""
                module example.turned

                data R = { p: Bool, q: Bool }

                behavior f : (a: Int) -> R
                let f (a) = R { p = check(a, 10), q = check(20 - a, 10) }

                let check (x: Int, limit: Int): Bool = x <= limit

                example f
                    | "eight" : (8) -> R { p = true, q = false }
                    | "nine" : (9) -> R { p = true, q = false }
                    | "ten" : (10) -> R { p = true, q = true }
                """);
        Map<PointRole, Map<String, Boolean>> hit = new LinkedHashMap<>();
        for (BorderObligationPointAssessment each : points) {
            Map<String, Boolean> byReading = new LinkedHashMap<>();
            for (BorderAssessment reading : each.readings()) {
                byReading.put(each.askedAt(reading).toString(),
                        each.owedAt(reading).coverage()
                                instanceof Measurement.Complete<ItemAssessment.Coverage>(var seen)
                                && ItemAssessment.Coverage.hit(seen));
            }
            hit.put(each.role(), byReading);
        }

        assertEquals(Map.of("BesideTheLine[side=ABOVE]", false, "BesideTheLine[side=BELOW]", true),
                hit.get(PointRole.OFF),
                () -> "the value beside the line where it fails is eleven for one call and nine"
                        + " for the other, and only the second has a row there: " + hit);
        assertEquals(Map.of("InTheRegion[side=ABOVE]", false, "InTheRegion[side=BELOW]", true),
                hit.get(PointRole.OUT),
                () -> "and the run past it is above eleven for one and below nine for the other,"
                        + " where the row at eight is the second's: " + hit);
    }

    /**
     * Which side of the author's line a point is on is said of the author's line, whichever way a
     * reading of it faces.
     *
     * <p>{@code x == limit} handed {@code 20 - a} is crossed below the author's ten where {@code a}
     * is above it, and the point beside the line on the author's lower side is said to be below
     * the line.
     */
    @Test
    void theSideOfAPointIsTheSideOfTheAuthorsLine() {
        List<BorderObligationPointAssessment> points = pointsOf("""
                module example.turned

                behavior f : (a: Int) -> Int
                let f (a) = if check(20 - a, 10) then 1 else 2

                let check (x: Int, limit: Int): Bool = x == limit
                """);
        for (BorderObligationPointAssessment each : points) {
            if (each.role() == PointRole.OFF) {
                assertEquals(each.at().side() == Towards.BELOW
                                ? " below the line" : " above the line", each.whichSide(),
                        () -> each.at() + " is on that side of the author's line");
            }
        }
        assertTrue(points.stream().anyMatch(each -> each.role() == PointRole.OFF),
                () -> "the line owes the values beside it: " + points);
    }

    /** The points the body comparisons of the module {@code example.turned} owe. */
    private static List<BorderObligationPointAssessment> pointsOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        List<BorderObligationPointAssessment> points = compilation.db().ask(
                new Adequacy.Obligations("example.turned", new GenerationScope.Module(),
                        HowALineIsRead.VALUES_COMPOSED)).value();
        assertNotNull(points, "the model under test compiles");
        return points.stream().filter(each -> each.id().provenance() instanceof RuleRef.Comparison c
                && c.origin().owner().equals(new WrittenOwner.Body("example.turned", "check")))
                .toList();
    }

    private static List<String> readings(BorderObligationPointAssessment point) {
        return point.met().keySet().stream().map(where -> where.target().left()).toList();
    }

    /** The points the guard's own line is owed a row at, by which of the four each is. */
    private static Map<PointRole, List<BorderObligationPointAssessment>> theGuardsPoints() {
        Map<PointRole, List<BorderObligationPointAssessment>> out = new LinkedHashMap<>();
        for (PointRole role : PointRole.values()) {
            out.put(role, new ArrayList<>());
        }
        for (BorderObligationPointAssessment each : obligations()) {
            // The guard's own line and not the ends the cases put on the field. Those are lines
            // too, and the run beside one of them is stopped by this guard — so they are owed to
            // the reading as much as this is, and telling them apart is asking which rule drew
            // them.
            if (each.id().provenance() instanceof RuleRef.Comparison) {
                out.get(each.role()).add(each);
            }
        }
        return out;
    }

    private static List<BorderObligationPointAssessment> obligations() {
        List<BorderObligationPointAssessment> points =
                compiled().db().ask(new Adequacy.Obligations("example.line",
                        new GenerationScope.Module(),
                        HowALineIsRead.VALUES_COMPOSED)).value();
        assertNotNull(points, "the model under test compiles");
        return points;
    }

    private static List<BorderAssessment> boundaries() {
        List<BorderAssessment> lines = compiled().db()
                .ask(new Adequacy.Boundaries("example.line", "check")).value();
        assertNotNull(lines, "the model under test compiles");
        return lines;
    }

    private static Compilation compiled() {
        Compilation compilation = Compilation.ofSource(CAPPED_APART, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
