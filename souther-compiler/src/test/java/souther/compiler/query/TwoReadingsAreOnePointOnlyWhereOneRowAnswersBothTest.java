package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.PointRole;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two readings of one line are one point where one row answers both, and two where it does not.
 *
 * <p>The two points against a line are values of the quantity, and the line settles them wherever it
 * is read: a row at the value is a row at the value, whichever case it was written under. The other
 * two are the regions either side, and a region is settled by the line together with whatever stops
 * it on the far side — so where the cases stop it in different places, a row inside one run says
 * nothing about the other.
 *
 * <p>Which is what {@link souther.compiler.partition.RegionBasis} carries, and this is the model
 * that tells the two apart: one guard, read under each case, with the cases capping the field at
 * different values.
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

    /**
     * The points against the line are one each; the run above it is one per case.
     *
     * <p>A row at {@code deadline = 11} answers the line under either case. A row inside the run
     * above it answers a run that stops at 20 or a run that stops at 30, and not both.
     */
    @Test
    void aRegionStoppedInTwoPlacesIsTwoPointsAndTheLineItselfIsOne() {
        Map<PointRole, List<BorderObligationPointAssessment>> byRole = theGuardsPoints();

        assertEquals(1, byRole.get(PointRole.ON).size(),
                () -> "one row answers the line: " + byRole.get(PointRole.ON));
        assertEquals(1, byRole.get(PointRole.OFF).size(),
                () -> "and one answers the value below it: " + byRole.get(PointRole.OFF));
        assertEquals(2, byRole.get(PointRole.IN).size(),
                () -> "the run above the line stops in two places: " + byRole.get(PointRole.IN));
        assertEquals(1, byRole.get(PointRole.OUT).size(),
                () -> "and the one below it stops at the end of the order for both: "
                        + byRole.get(PointRole.OUT));
    }

    /** And what is one point is read under each case, while what is two is read under one. */
    @Test
    void aPointIsReadUnderEveryCaseThatSharesIt() {
        Map<PointRole, List<BorderObligationPointAssessment>> byRole = theGuardsPoints();

        assertEquals(List.of("check/r@P.deadline", "check/r@T.deadline"),
                readings(byRole.get(PointRole.ON).get(0)),
                "the line is read under each case");
        for (BorderObligationPointAssessment each : byRole.get(PointRole.IN)) {
            assertEquals(1, each.met().size(),
                    () -> "and a run only one case has is read under that one: " + readings(each));
        }
    }

    /**
     * A reading offered twice is refused rather than counted twice.
     *
     * <p>What a search of one of them came to would stand for the other, chosen by the order the
     * walk took — so two readings this cannot tell apart are not two readings, and saying so is the
     * only answer that does not depend on which arrived first.
     */
    @Test
    void aReadingOfferedTwiceIsRefused() {
        List<BorderAssessment> lines = boundaries();
        List<BorderAssessment> twice = new ArrayList<>(lines);
        twice.addAll(lines);

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> BorderObligationPointAssessment.across(Map.of("check", twice),
                        point -> "the line"));
        assertTrue(refused.getMessage().contains("twice"), refused::getMessage);
    }

    private static List<String> readings(BorderObligationPointAssessment point) {
        return point.met().keySet().stream().map(Object::toString).toList();
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
                        new GenerationScope.Module())).value();
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
