package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.query.PartitionEvidence;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a row for one of a border's points is looked for.
 *
 * <p>Issue #911. A border on an arithmetic form is met by solving the form for a level, and the box
 * that search runs in was each position's declared domain — what its type and that type's
 * invariants leave. A guard draws a threshold and narrows no domain, so a border a guard owes was
 * searched for over the whole of what the positions could ever hold rather than over the region
 * that reaches the guard.
 *
 * <p>Two things follow and they are the same fault from either side. Too wide, and a level with an
 * answer in the region comes back as one the search did not reach. Not used at all, and the row
 * offered for a level is one a rule above the guard refuses.
 *
 * <p>The first is measured as a pair rather than against a constant. The same equation over the
 * same region is written twice — once with the bounds on the guards and once with them on the types
 * — and what a search makes of it may not depend on which. Held against a constant instead, a test
 * would say what this compiler manages today rather than that the two agree.
 */
class ARowForABorderIsSearchedForInTheRegionThatReachesItTest {

    /** The bounds written as guards, so nothing narrows a declared domain. */
    private static final String ON_GUARDS = """
            module example.checkout

            data Small = Int
            data Large = Int

            data Rejected = { reason: Int }
            data Order = { total: Int }
            data Result = Rejected | Order

            behavior checkout : (x: Small, y: Large) -> Result
                constructs Rejected, Order
            let checkout (x, y) = {
                guard x.value >= 0 else Rejected { reason = 1 }
                guard x.value <= 20 else Rejected { reason = 2 }
                guard y.value >= 0 else Rejected { reason = 3 }
                guard y.value <= 10 else Rejected { reason = 4 }
                guard Int.add(x.value, Int.multiply(2, y.value)) <= 16 else Rejected { reason = 5 }
                Order { total = x.value }
            }

            example checkout
                | "ok" : (Small(1), Large(1)) -> Order { total = 1 }
            """;

    /** The same region, written where the declarations carry it. */
    private static final String ON_TYPES = """
            module example.checkout

            data Small = Int
                invariant value >= 0
                invariant value <= 20
            data Large = Int
                invariant value >= 0
                invariant value <= 10

            data Rejected = { reason: Int }
            data Order = { total: Int }
            data Result = Rejected | Order

            behavior checkout : (x: Small, y: Large) -> Result
                constructs Rejected, Order
            let checkout (x, y) = {
                guard Int.add(x.value, Int.multiply(2, y.value)) <= 16 else Rejected { reason = 5 }
                Order { total = x.value }
            }

            example checkout
                | "ok" : (Small(1), Large(1)) -> Order { total = 1 }
            """;

    /** A guard above the form's, which no row reaching the form's line may fail. */
    private static final String A_GUARD_ABOVE = """
            module example.checkout

            data Small = Int
                invariant value >= 0
                invariant value <= 20
            data Large = Int
                invariant value >= 0
                invariant value <= 10

            data Rejected = { reason: Int }
            data Order = { total: Int }
            data Result = Rejected | Order

            behavior checkout : (x: Small, y: Large) -> Result
                constructs Rejected, Order
            let checkout (x, y) = {
                guard y.value <= 6 else Rejected { reason = 1 }
                guard Int.add(x.value, Int.multiply(2, y.value)) <= 16 else Rejected { reason = 5 }
                Order { total = x.value }
            }

            example checkout
                | "ok" : (Small(1), Large(1)) -> Order { total = 1 }
            """;

    /**
     * A level the region has an answer at, composed.
     *
     * <p>{@code x = 1, y = 8} is at {@code x + 2y = 17} and passes every guard above the one that
     * draws the line. Searched over the declared domains, {@code x} is bounded nowhere, one value
     * of it is tried, and the point comes back as one the search stopped short of.
     */
    @Test
    void aLevelTheRegionHasAnAnswerAtIsComposed() {
        ItemAssessment.Owed off = owed(pointAt(ON_GUARDS, "x + 2 * y = 17"));

        assertInstanceOf(ItemAssessment.Attempt.Built.class, off.attempt(),
                "a row at the level exists in the region that reaches the guard");
    }

    /**
     * The same equation over the same region, answered the same way.
     *
     * <p>What moves between the two models is where the bounds are written, and that is not
     * something a coverage answer is about.
     */
    @Test
    void whereTheBoundsAreWrittenDoesNotMoveTheAnswer() {
        for (String level : List.of("x + 2 * y = 16", "x + 2 * y = 17")) {
            assertEquals(owed(pointAt(ON_TYPES, level)).attempt().getClass(),
                    owed(pointAt(ON_GUARDS, level)).attempt().getClass(),
                    "the same line over the same region, at " + level);
        }
    }

    /**
     * A row offered for a level is one that reaches the guard that owes it.
     *
     * <p>Both points of {@code x + 2y} were answered with {@code y = 8}, which the guard above
     * refuses. The measure was right — no row is at either point — and what was wrong is the piece
     * of work an author was handed.
     */
    @Test
    void aRowOfferedForALevelReachesTheGuardThatOwesIt() {
        for (String level : List.of("x + 2 * y = 16", "x + 2 * y = 17")) {
            ItemAssessment.Attempt attempt = owed(pointAt(A_GUARD_ABOVE, level)).attempt();
            ItemAssessment.Attempt.Built built = assertInstanceOf(
                    ItemAssessment.Attempt.Built.class, attempt, "a row was composed at " + level);
            assertTrue(largeIn(built.row()) <= 6,
                    "the guard above holds y at six, and " + written(built.row())
                            + " never reaches the line at " + level);
        }
    }

    /** What the row puts in the second position, as a number. */
    private static long largeIn(souther.compiler.partition.Generator.GeneratedRow row) {
        String text = row.inputs().get(1).text();
        return Long.parseLong(text.substring(text.indexOf('(') + 1, text.lastIndexOf(')')));
    }

    private static String written(souther.compiler.partition.Generator.GeneratedRow row) {
        return row.inputs().stream().map(FixtureTemplate::text).toList().toString();
    }

    /** The one point of one border, found by the line and the level it names. */
    private static BorderAssessment.Point pointAt(String source, String level) {
        List<BorderAssessment.Point> found =
                BorderAssessment.pointsOf(evidence(source).boundaries()).stream()
                        .filter(point -> point.label() != null && point.label().endsWith(level))
                        .toList();
        assertEquals(1, found.size(),
                "one point is named `" + level + "`, and these are the points: "
                        + BorderAssessment.pointsOf(evidence(source).boundaries()).stream()
                                .map(BorderAssessment.Point::label).toList());
        return found.get(0);
    }

    private static ItemAssessment.Owed owed(BorderAssessment.Point point) {
        return assertInstanceOf(ItemAssessment.Owed.class, point.item(),
                "a row is owed at " + point.label());
    }

    private static PartitionEvidence evidence(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        Map<String, PartitionEvidence> all = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
        assertNotNull(all, "the model under test compiles");
        return all.get("checkout");
    }
}
