package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A run gets to a place only past everything worked out on the way, and past an operator only on
 * the operands it answers on.
 *
 * <p>{@code a + 1} over {@code Int} answers where {@code a} is below the greatest {@code Int}. A
 * line drawn past it is drawn on what every run getting there holds, and that is what the guards
 * hold together with where the sum answers. Where those leave nothing, no run gets to the line and
 * no row is owed at it; where they leave something, the line is drawn as it always was. The same
 * goes for the applications of a closure one after another: the next is made only where the one
 * before it got past its operators.
 *
 * <p>Each holding is shown beside a control the same but for one value, where a run does get
 * there, so that a line dropped is a line dropped for this reason.
 */
class ARunGetsPastWhatItWorksOutOnlyWhereItsOperatorsAnswerTest {

    private static final String GREATEST = "9223372036854775807";

    private static final String BELOW_THE_GREATEST = "9223372036854775806";

    private static String report(String body) {
        Compilation compilation = Compilation.ofSource("""
                module w1
                behavior f : (xs: List<Int>, n: Int, a: Int, b: Int) -> Ok | No
                let f (xs, n, a, b) = {
                %s
                    Ok
                }
                """.formatted(body), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** The points owed at the comparison written at {@code at}, by role, as the report says each. */
    private static List<String> pointsAt(String report, String at) {
        return report.lines().map(String::strip)
                .filter(line -> line.contains("point (comparison@" + at + ")"))
                .filter(line -> line.startsWith("?") || line.startsWith("!"))
                .map(line -> line.replaceAll(".* the (ON|OFF|IN|OUT) point .*", "$1"))
                .distinct().toList();
    }

    /** Whether the report says the comparison at {@code at} drew no line about {@code about}
     *  because nothing that arrives there holds a value at it. */
    private static boolean nothingArrivesAt(String report, String at, String about) {
        return report.lines().anyMatch(line -> line.contains("no line: comparison@" + at)
                && line.contains("about `" + about + "`"));
    }

    @Test
    void aSumNoRunGetsPastLeavesTheLineAfterItWithNothingArriving() {
        String report = report("""
                    guard a == %s else No
                    let c = a + 1
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(nothingArrivesAt(report, "6:9", "b"), report);
        assertEquals(List.of(), pointsAt(report, "6:9"), report);
    }

    @Test
    void aSumARunGetsPastLeavesTheLineAfterItOwed() {
        String report = report("""
                    guard a == %s else No
                    let c = a + 1
                    guard b > 3 else No""".formatted(BELOW_THE_GREATEST));
        assertFalse(nothingArrivesAt(report, "6:9", "b"), report);
        assertEquals(List.of("ON", "OFF", "IN", "OUT"), pointsAt(report, "6:9"), report);
    }

    /** The left of a join is worked out before the right, so a right past a left that stops is
     *  reached by nothing. */
    @Test
    void aSumOnTheLeftOfAJoinStopsTheRight() {
        String report = report("""
                    guard a == %s else No
                    guard a + 1 > 0 && b > 3 else No""".formatted(GREATEST));
        assertTrue(nothingArrivesAt(report, "5:22", "b"), report);
        assertEquals(List.of(), pointsAt(report, "5:22"), report);
    }

    /**
     * And the right of a join is worked out only where the left leaves it open: where the left
     * settles it, a run goes on past the join whatever the right would have done. A sum that stops
     * on the right stops only the runs that work it out.
     */
    @Test
    void aSumOnTheRightOfAJoinStopsOnlyTheRunsThatWorkItOut() {
        String report = report("""
                    guard a == %s else No
                    guard b > 3 || a + 1 > 0 else No
                    guard n > 5 else No""".formatted(GREATEST));
        assertFalse(nothingArrivesAt(report, "6:9", "n"), report);
        assertEquals(List.of("ON", "OFF", "IN", "OUT"), pointsAt(report, "6:9"), report);
    }

    /** Named or written where it is compared, a sum stops a run on the same operands. */
    @Test
    void aSumGivenANameStopsARunWhereTheSameSumWrittenOutDoes() {
        String named = report("""
                    guard a == %s else No
                    let c = a + 1
                    guard c > 0 else No
                    guard b > 3 else No""".formatted(GREATEST));
        String written = report("""
                    guard a == %s else No
                    guard a + 1 > 0 else No
                    guard b > 3 else No""".formatted(GREATEST));
        assertTrue(nothingArrivesAt(named, "7:9", "b"), named);
        assertTrue(nothingArrivesAt(written, "6:9", "b"), written);
    }

    /** A closure applied to the values a list was written with is applied to the next only past
     *  the one before it. */
    @Test
    void anApplicationPastOneThatStopsIsMadeByNoRun() {
        String report = report("""
                    guard a == %s else No
                    guard List.length(List.filter(x -> x + 1 > 0, [a, b])) >= 1 else No"""
                .formatted(GREATEST));
        assertEquals(List.of(), pointsAt(report, "5:42"), report);
    }

    /**
     * Two operators coming to one form are two operators. A {@code Decimal} sum and an {@code Int}
     * sum over the same number answer in different places, and the closure's next application is
     * made only past both.
     */
    @Test
    void twoOperatorsComingToOneFormAreEachGotPast() {
        String report = report("""
                    guard a == %s else No
                    guard List.length(List.filter(x -> Decimal.fromInt(x) + 1.0m > Decimal.fromInt(x + 1) + Decimal.fromInt(x), [a, b])) >= 1 else No"""
                .formatted(GREATEST));
        assertEquals(List.of(), pointsAt(report, "5:62"), report);
    }

    @Test
    void anApplicationPastOneThatAnswersIsMade() {
        String report = report("""
                    guard a == %s else No
                    guard List.length(List.filter(x -> x + 1 > 0, [a, b])) >= 1 else No"""
                .formatted(BELOW_THE_GREATEST));
        assertEquals(List.of("ON", "OFF", "IN", "OUT"), pointsAt(report, "5:42"), report);
    }
}
