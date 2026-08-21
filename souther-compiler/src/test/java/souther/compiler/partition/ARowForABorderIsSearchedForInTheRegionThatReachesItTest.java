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
     * A line inside the arm a condition fails on, which is the other half of the same reading.
     *
     * <p>Reaching the {@code else} arm proves the condition did not hold, so the region there is
     * where {@code y} is under seven rather than where it is past six. A reading that took the arm
     * for the condition — or the condition for the arm — would narrow this one the wrong way round,
     * and the row it offered would be refused for the opposite reason.
     *
     * <p>Written so that the answer differs. A search of the declared box solves this line by trying
     * the positions in the order the form names them, which takes {@code y} at its largest first —
     * so a line whose arm wants a large {@code y} is answered the same either way, and a test built
     * on one would pass without the region being read at all.
     */
    private static final String INSIDE_THE_OTHER_ARM = """
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
            let checkout (x, y) =
                if y.value >= 7 then Order { total = x.value }
                else {
                    guard Int.add(x.value, Int.multiply(2, y.value)) <= 16
                        else Rejected { reason = 5 }
                    Order { total = 1 }
                }

            example checkout
                | "ok" : (Small(1), Large(1)) -> Order { total = 1 }
            """;

    /** A behavior over the same two bounded positions, with {@code body} for a body. */
    private static String checkout(String body) {
        return """
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
                %s
                    Order { total = x.value }
                }

                example checkout
                    | "ok" : (Small(1), Large(1)) -> Order { total = 1 }
                """.formatted(body);
    }

    /** The form's own line, which every model below draws. */
    private static final String THE_FORM =
            "Int.add(x.value, Int.multiply(2, y.value)) <= 16";

    /**
     * The bounds written as one condition rather than as four guards.
     *
     * <p>The same model. Running conditions together with {@code &&} and writing them one after
     * another state the same thing, and a coverage answer that moved between them would be a fact
     * about how the author spelled the condition.
     */
    @Test
    void spellingTheConditionsAsOneChainDoesNotMoveTheAnswer() {
        // The bounds on the guards and nowhere else, the same as `ON_GUARDS`. Declared on the types
        // as well, the region would have nothing to add and this would pass without being read.
        String chained = """
                module example.checkout

                data Small = Int
                data Large = Int

                data Rejected = { reason: Int }
                data Order = { total: Int }
                data Result = Rejected | Order

                behavior checkout : (x: Small, y: Large) -> Result
                    constructs Rejected, Order
                let checkout (x, y) = {
                    guard x.value >= 0
                        && x.value <= 20
                        && y.value >= 0
                        && y.value <= 10
                        && Int.add(x.value, Int.multiply(2, y.value)) <= 16
                        else Rejected { reason = 5 }
                    Order { total = x.value }
                }

                example checkout
                    | "ok" : (Small(1), Large(1)) -> Order { total = 1 }
                """;

        for (String level : List.of("x + 2 * y = 16", "x + 2 * y = 17")) {
            assertEquals(owed(pointAt(ON_GUARDS, level)).attempt().getClass(),
                    owed(pointAt(chained, level)).attempt().getClass(),
                    "one chain and four guards say the same thing, at " + level);
            assertInstanceOf(ItemAssessment.Attempt.Built.class,
                    owed(pointAt(chained, level)).attempt(),
                    "and both of them find a row at " + level);
        }
    }

    /**
     * The second operand of a disjunction runs where the first failed.
     *
     * <p>A condition stops as soon as it is settled, so the form's line is only ever reached by rows
     * with {@code y} at six or under — the same region the guard above it gave, arriving by the
     * other operator.
     */
    @Test
    void theSecondOperandOfADisjunctionStandsWhereTheFirstFailed() {
        String either = checkout(
                "    guard y.value >= 7 || %s else Rejected { reason = 5 }".formatted(THE_FORM));

        assertTrue(largeIn(built(either, "x + 2 * y = 16").row()) <= 6,
                "nothing with y at seven or above reaches the second operand");
    }

    /**
     * And a comparison nested under both operators takes what each of them left.
     *
     * <p>{@code A && (B || C)} puts {@code C} where {@code A} held and {@code B} did not, which no
     * reading of the fork's arms says: the fork's {@code else} arm holds rows that failed
     * {@code A}, rows that failed both {@code B} and {@code C}, and rows that never reached
     * {@code C} at all.
     */
    @Test
    void aComparisonUnderBothOperatorsTakesWhatEachOfThemLeft() {
        String nested = checkout("""
                    guard x.value <= 20 && (y.value >= 7 || %s)
                        else Rejected { reason = 5 }""".formatted(THE_FORM));

        assertTrue(largeIn(built(nested, "x + 2 * y = 16").row()) <= 6,
                "nothing with y at seven or above reaches the third comparison");
    }

    /**
     * A condition the arithmetic cannot read narrows nothing.
     *
     * <p>The direction the whole region depends on. A product of two positions is outside what the
     * form reading takes in, so nothing is established by passing it — and a region narrowed on it
     * would be narrower than the rows that arrive, which is what turns a search that finds nothing
     * into a claim that nothing is there.
     */
    @Test
    void aConditionNothingCouldReadNarrowsNothing() {
        String alone = checkout("    guard %s else Rejected { reason = 5 }".formatted(THE_FORM));
        String under = checkout("""
                    guard Int.multiply(x.value, y.value) <= 50 else Rejected { reason = 1 }
                    guard %s else Rejected { reason = 5 }""".formatted(THE_FORM));

        for (String level : List.of("x + 2 * y = 16", "x + 2 * y = 17")) {
            assertEquals(written(built(alone, level).row()), written(built(under, level).row()),
                    "an unread condition above changes nothing at " + level);
        }
    }

    /** The row one point was answered with, where one was built at all. */
    private static ItemAssessment.Attempt.Built built(String source, String level) {
        return assertInstanceOf(ItemAssessment.Attempt.Built.class,
                owed(pointAt(source, level)).attempt(), "a row was composed at " + level);
    }

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

    /**
     * A row for a line in the arm a condition fails on stands where that condition fails.
     *
     * <p>The same rule as the arm above it, read the other way round. Nothing in this arm holds
     * {@code y} at six or under, and a row that does never arrives at the guard.
     */
    @Test
    void aRowForALineInsideTheOtherArmStandsWhereThatConditionFails() {
        ItemAssessment.Attempt.Built built = assertInstanceOf(ItemAssessment.Attempt.Built.class,
                owed(pointAt(INSIDE_THE_OTHER_ARM, "x + 2 * y = 16")).attempt(),
                "a row at the level exists in the arm the condition fails on");

        assertTrue(largeIn(built.row()) <= 6,
                "nothing at seven or above reaches this arm, and " + written(built.row())
                        + " was offered for a line inside it");
    }

    /** What the row puts in the second position, as a number. */
    private static long largeIn(souther.compiler.partition.Generator.GeneratedRow row) {
        return numberIn(row.inputs().get(1).text());
    }

    /** The number a written newtype holds. */
    private static long numberIn(String written) {
        return Long.parseLong(
                written.substring(written.indexOf('(') + 1, written.lastIndexOf(')')));
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
