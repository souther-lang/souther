package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderObligationPointAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.GenerationScope;
import souther.compiler.query.HowALineIsRead;
import souther.compiler.partition.ObligationIdentity;
import souther.compiler.query.Composition;
import souther.compiler.query.OfferingRequest;
import souther.compiler.query.Settlements;
import souther.compiler.partition.BorderObligationPoint;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Everything owed at a point is one item of the offering, and a point is the author's.
 *
 * <p>A region beside a comparison a body wrote is one of the four points of the author's line,
 * however many places what reaches the position stops each reading's run: the author wrote one
 * guard, and the region beside it is one row to write. What stopped the run is where that reading
 * looks for the row, and is no part of which point it is.
 *
 * <p><b>And the items are the points and nothing else.</b> Read as the places a row is composed at,
 * an obligation could fall in no item universe: nothing counts a row as settling it, nothing can say
 * it is answered, and a note saying no row is offered for it prints over the row standing at it.
 */
class EveryThingOwedAtAPointIsAnItemOfItsOwnTest {

    /**
     * One position whose line is stopped in two places.
     *
     * <p>Two helpers compare the same position at the same value, so the region above the body's
     * own line at four runs up to a line each of them drew. The values coincide; the rules do not.
     */
    private static final String TWO_STOPS = """
            module example.stops

            data Hours = Int
                invariant value >= 0 && value <= 24

            let over (h: Hours): Int = if h.value > 8 then 1 else 0

            let also (h: Hours): Int = if h.value > 8 then 2 else 0

            behavior tally : (worked: Hours) -> Int

            let tally (worked) = if worked.value > 4 then over(worked) + also(worked) else 0
            """;

    /**
     * The region beside a body's line is one item, wherever the run is stopped.
     *
     * <p>The line at four is owed a run above it, and the run stops at whichever helper's line
     * reaches the position — two of them, at one value. One guard the author wrote and one region
     * beside it: one thing to be told about.
     */
    @Test
    void aRegionBesideABodysLineStoppedInTwoPlacesIsOneItem() {
        Compilation compilation = compiled();
        Settlements table = Settlements.of(compilation.db(), composed(compilation));

        Map<String, Set<BorderObligationPoint>> byLineAndRole = new LinkedHashMap<>();
        for (BorderObligationPoint point : pointsOf(table)) {
            byLineAndRole.computeIfAbsent(point.line() + " " + point.role(),
                    _ -> new LinkedHashSet<>()).add(point);
        }
        assertTrue(byLineAndRole.values().stream().allMatch(at -> at.size() == 1),
                "no point of this model is owed more than once: " + byLineAndRole);
        assertTrue(pointsOf(table).stream().anyMatch(point -> point.line().at().isEmpty()
                        && point instanceof BorderObligationPoint.InRegion),
                "and the region beside the body's line is among them: " + byLineAndRole);
    }

    /**
     * Every open point is one item, and nothing else is.
     *
     * <p>The whole of what an offering is asked. A point is one piece of work however many readings
     * of the line there are and whoever owes it, so the items are the points this module answers
     * for that the measurement says are worth looking for — one apiece.
     *
     * <p>Written as the two sets rather than as a count, which holds while a point this dropped is
     * made up for by one it invented.
     */
    @Test
    void everyOpenPointIsOneItemAndNothingElseIs() {
        Compilation compilation = compiled();
        List<BorderObligationPointAssessment> points = compilation.db()
                .ask(new Adequacy.Obligations("example.stops", new GenerationScope.Module(),
                        HowALineIsRead.VALUES_COMPOSED)).value();
        assertNotNull(points, "the model under test is measured");

        Set<BorderObligationPoint> open = new LinkedHashSet<>();
        for (BorderObligationPointAssessment each : points) {
            // What this module answers for. A line owed to declarations elsewhere is one its values
            // are held to and somebody else's to write a row at.
            boolean here = !each.ownersIn("example.stops").isEmpty() || each.owedToTheReading();
            if (here && each.owed().worthSearching()) {
                open.add(each.point());
            }
        }
        assertFalse(open.isEmpty(), "the model under test leaves points to look for");

        Settlements table = Settlements.of(compilation.db(), composed(compilation));
        assertEquals(open, new LinkedHashSet<>(pointsOf(table)),
                "every open point is asked about, once");
        assertEquals(pointsOf(table).size(), new LinkedHashSet<>(pointsOf(table)).size(),
                "and no point is asked about twice: " + pointsOf(table));
    }

    /** The points the offering was asked about, in the order it asks them. */
    private static List<BorderObligationPoint> pointsOf(Settlements table) {
        List<BorderObligationPoint> asked = new ArrayList<>();
        for (ObligationIdentity item : table.requested()) {
            if (item instanceof ObligationIdentity.OfALine(var point)) {
                asked.add(point);
            }
        }
        return asked;
    }

    private static Compilation compiled() {
        Compilation compilation = Compilation.ofSource(TWO_STOPS, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static Composition composed(Compilation compilation) {
        Map<String, Adequacy.Filling> generated =
                Adequacy.generatedOf(compilation.db(), "example.stops");
        assertNotNull(generated, "the model under test compiles: " + compilation.errors());
        return Composition.composed(OfferingRequest.overTheModule("example.stops"), generated,
                Adequacy.accountFor(compilation.db(), "example.stops",
                        new GenerationScope.Module()));
    }
}
