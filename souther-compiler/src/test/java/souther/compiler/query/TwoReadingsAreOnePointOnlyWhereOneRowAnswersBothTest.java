package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.Demand;
import souther.compiler.partition.PointRole;

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
            if (each.id().provenance() instanceof souther.compiler.check.RuleRef.Comparison) {
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
