package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A rule written in a body draws a line and does not move where the position runs.
 *
 * <p>Two things bound the run a border's {@code IN} point asks for: the places the rules part the
 * position's values, and the ends the rules leave it between. The first is every rule that cuts the
 * quantity, a body's own among them; the second is what the declarations say a position holds, and a
 * body says nothing about that — it cannot refuse a value it is given, only branch on it.
 *
 * <p>Which is what says who owes a row inside such a run. A run bounded by a body's line is that
 * body's; a run bounded by an end the declarations leave is owed wherever the type is carried. So
 * the two are told apart by what bounds them, and this is where the compiler's answer to that is
 * pinned: a body's rule reaches a run as a place the values part and never as an end.
 */
class WhereAPositionRunsIsNotSomethingABodyMovesTest {

    /** A body's comparison, with nothing declared about the position at all. */
    private static final String GUARDED = """
            module example.projection

            data Amount = Int

            data Small
            data Large
            data Size = Small | Large

            behavior guarded : (a: Amount) -> Size
            let guarded (a) = if a.value <= 10 then Small else Large

            example guarded
                | "y" : (Amount(1)) -> Small
            """;

    /** An {@code ensures} clause, which is written on a behavior and draws a line the same way. */
    private static final String STATED = """
            module example.stated

            data R = { a: Int, b: Int }
            data Found
            data Missing

            behavior f : (r: R) -> Found | Missing
                ensures Found -> r.a >= 5 && r.b >= 5
            let f (r) = if r.a >= 30 * 2 then Found else Missing

            example f
                | "one" : (R { a = 1, b = 1 }) -> Missing
            """;

    /**
     * A comparison in a body parts the values and leaves the position running as far as it did.
     *
     * <p>Nothing is declared about {@code Amount}, so the position runs the whole of its carrier.
     * The comparison at ten divides it, and the two runs either side of that line are bounded by the
     * line and by nothing else — an {@code Int} has no end for them to stop at.
     */
    @Test
    void aComparisonInABodyPartsThePositionAndLeavesItsEndsAlone() {
        Criterion.Within inside = runAt(GUARDED, "example.projection", "a = 10", PointRole.IN);

        assertNotNull(inside.band().over(), "the line it is named for parts the values there");
        assertNull(inside.band().from(),
                "and the rules leave the position no end below, the comparison included");
        assertNull(inside.band().to(), "nor above");
        assertEquals("guarded/a in a < 10", saidAt(GUARDED, "example.projection", "a = 10",
                PointRole.IN), "so the run is written from its line and runs on");
    }

    /**
     * And an {@code ensures} clause is a body's rule too.
     *
     * <p>{@code r.a} is bounded below by the clause's own line at five and above by the comparison
     * at sixty, and both of those are places the values part. Neither is an end: the position runs
     * as far as an {@code Int} does either way.
     */
    @Test
    void anEnsuresClauseDrawsALineTheSameWay() {
        Criterion.Within inside = runAt(STATED, "example.stated", "r.a = 5", PointRole.IN);

        assertNotNull(inside.band().under(), "its own line below");
        assertNotNull(inside.band().over(), "the comparison's line above");
        assertNull(inside.band().from(), "and no end the rules leave, below");
        assertNull(inside.band().to(), "or above");
    }

    /** The run one point of one border asks a row to land in. */
    private static Criterion.Within runAt(String model, String module, String label,
                                          PointRole role) {
        Criterion criterion = borderAt(model, module, label).border().demand(role).criterion();
        if (!(criterion instanceof Criterion.Within inside)) {
            throw new AssertionError("the " + role + " point of " + label
                    + " is not a run of the position: " + criterion);
        }
        return inside;
    }

    /** What a report writes over a row at that point. */
    private static String saidAt(String model, String module, String label, PointRole role) {
        return borderAt(model, module, label).points().stream()
                .filter(point -> point.role() == role).findFirst()
                .orElseThrow(() -> new AssertionError("no " + role + " point of " + label))
                .said();
    }

    private static BorderAssessment borderAt(String model, String module, String label) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> boundaries =
                Adequacy.boundariesOf(compilation.db(), module);
        assertNotNull(boundaries, "the model under test compiles");
        return boundaries.values().stream().flatMap(List::stream)
                .filter(each -> each.label().equals(label)).findFirst()
                .orElseThrow(() -> new AssertionError(label + " is not a line of this model: "
                        + boundaries.values().stream().flatMap(List::stream)
                                .map(BorderAssessment::label).toList()));
    }
}
