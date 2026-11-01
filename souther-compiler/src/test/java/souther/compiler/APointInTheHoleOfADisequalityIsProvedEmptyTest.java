package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.check.ComparisonClaim;
import souther.compiler.partition.PointRole;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderObligationPointAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A point that lies only where a disequality has taken a value out of a whole-numbered position
 * is one no row can stand at, as a point outside an interval guard is.
 *
 * <p>The hole is inside the run the position is projected onto, so only the region's own algebra
 * finds it, and it is handed the point's bounds as numbers of the position. What is asked of the
 * report is the answer for one line of one behavior, read off the account and not off the page: a
 * page names several comparisons and several points, and a phrase found somewhere on it says
 * nothing about which of them it is about.
 */
class APointInTheHoleOfADisequalityIsProvedEmptyTest {

    /** The comparison that singles 50 out, then a threshold the single value is already taken from. */
    private static final String THRESHOLD_AFTER_THE_EQUALITY = """
            module m

            behavior f : (n: Int) -> Int

            let f (n) = if n == 50 then 3 else (if n >= 50 then 1 else 2)

            example f
                | (50) -> 3
                | (49) -> 2
                | (51) -> 1
                | (0) -> 2
                | (60) -> 1
            """;

    /** The same threshold read from below. */
    private static final String BELOW_THE_EQUALITY = """
            module m

            behavior f : (n: Int) -> Int

            let f (n) = if n == 50 then 3 else (if n <= 50 then 1 else 2)

            example f
                | (50) -> 3
                | (49) -> 1
                | (51) -> 2
                | (0) -> 1
                | (60) -> 2
            """;

    /** The threshold's ON point is 51, which the hole leaves; its OFF point is 50, which it does not. */
    private static final String THRESHOLD_BESIDE_THE_HOLE = """
            module m

            behavior f : (n: Int) -> Int

            let f (n) = if n == 50 then 3 else (if n >= 51 then 1 else 2)

            example f
                | (50) -> 3
                | (49) -> 2
                | (51) -> 1
                | (0) -> 2
                | (60) -> 1
            """;

    /** The hole reached through a callee: the first arm of {@code clamp} draws the line. */
    private static final String THROUGH_A_CALLEE = """
            module m

            behavior clamp : (n: Int) -> Int

            let clamp (n) = if n > 50 then 50 else n

            behavior full : (n: Int) -> Bool

            let full (n) = clamp(n) == 50

            example full
                | (50) -> true
                | (49) -> false
                | (0) -> false
            """;

    private static final String DATES = """
            module m

            behavior f : (d: Date) -> Int

            let f (d) = if d == Date("2024-03-01") then 3 else (if d >= Date("2024-03-01") then 1 else 2)

            example f
                | (Date("2024-03-01")) -> 3
                | (Date("2024-02-29")) -> 2
                | (Date("2024-03-02")) -> 1
                | (Date("2020-01-01")) -> 2
                | (Date("2030-01-01")) -> 1
            """;

    private static final String DECIMALS = """
            module m

            behavior f : (x: Decimal) -> Int

            let f (x) = if x == 50.0m then 3 else (if x >= 50.0m then 1 else 2)

            example f
                | (50.0m) -> 3
                | (49.0m) -> 2
                | (51.0m) -> 1
                | (0.0m) -> 2
                | (60.0m) -> 1
            """;

    /** A carrier whose places count in days: the number the region holds is the count of the date. */
    @Test
    void theOnPointOfADateThresholdTakenFromTheEqualityIsOneNoRowCanStandAt() {
        assertEquals(List.of("ON Refuted", "OFF Met", "OUT Met"),
                pointsOf(DATES, "f", ComparisonClaim.Cut.class));
    }

    /** A carrier with no next value: the point in the hole is refuted and none is invented beside it. */
    @Test
    void theOnPointOfADecimalThresholdTakenFromTheEqualityIsOneNoRowCanStandAt() {
        assertEquals(List.of("ON Refuted", "OUT Met"),
                pointsOf(DECIMALS, "f", ComparisonClaim.Cut.class));
    }

    @Test
    void theOnPointOfAThresholdTakenFromTheEqualityIsOneNoRowCanStandAt() {
        assertEquals(List.of("ON Refuted", "OFF Met", "OUT Met"),
                pointsOf(THRESHOLD_AFTER_THE_EQUALITY, "f", ComparisonClaim.Cut.class),
                "the threshold's ON point is the value the equality took, and its other points are"
                        + " rows");
        assertEquals(List.of("ON Met", "OFF Met", "OFF Met", "OUT Met", "OUT Met"),
                pointsOf(THRESHOLD_AFTER_THE_EQUALITY, "f", ComparisonClaim.Singled.class),
                "the equality's own points are untouched");
    }

    @Test
    void theOnPointOfAThresholdTakenFromTheEqualityFromBelowIsOneNoRowCanStandAt() {
        assertEquals(List.of("ON Refuted", "OFF Met", "OUT Met"),
                pointsOf(BELOW_THE_EQUALITY, "f", ComparisonClaim.Cut.class));
    }

    @Test
    void aPointTheHoleLeavesIsNotRefutedAndOneInItIs() {
        assertEquals(List.of("ON Met", "OFF Refuted", "IN Met"),
                pointsOf(THRESHOLD_BESIDE_THE_HOLE, "f", ComparisonClaim.Cut.class),
                "51 is a value the else branch takes and 50 is the value it does not");
    }

    @Test
    void theOffPointOfALineReadThroughACalleeIsOneNoRowCanStandAtWhileItsGapIsStillOwed() {
        assertEquals(List.of("ON Unmet", "OFF Refuted", "IN Unmet"),
                pointsOf(THROUGH_A_CALLEE, "full", ComparisonClaim.Cut.class),
                "the first arm of clamp draws the line; 50 is outside the case it decides in, and"
                        + " 51 and the values past it are a gap no row fills");
    }

    /**
     * The points of the one line of {@code behavior} whose claim is a {@code claim}, each as its
     * role and what became of the obligation.
     */
    private static List<String> pointsOf(String model, String behavior,
                                         Class<? extends ComparisonClaim> claim) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        List<String> out = new ArrayList<>();
        for (AdequacyReport.BehaviorReport each
                : AdequacyReport.of(compilation).modules().get(0).behaviors()) {
            if (!each.name().equals(behavior)) {
                continue;
            }
            for (BorderObligationPointAssessment point : each.account()) {
                if (claim.isInstance(point.point().line().line().facts().claim())) {
                    PointRole role = point.point().role();
                    out.add(role + " "
                            + point.item().disposition().getClass().getSimpleName());
                }
            }
        }
        return out;
    }
}
