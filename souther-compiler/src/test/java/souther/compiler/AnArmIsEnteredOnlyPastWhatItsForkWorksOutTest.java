package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.LabeledRegion;
import souther.compiler.diag.msg.DeadBranchMessage;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An arm of a fork is entered only by a run that got past working out what the fork decides on,
 * and past everything worked out before it.
 *
 * <p>{@code a + 1} over {@code Int} answers where {@code a} is below the greatest {@code Int}. A
 * fork deciding on it, or standing past it, is entered by no run where the guards hold {@code a} at
 * the greatest, so neither arm is reached: the fork is reported as one nothing reaches, with the
 * evaluation the way there has to get past pointed at. A fork inside one of those arms is not
 * reported again. And a quotient answers only where its divisor is not nought, so a fork past one
 * asking whether the divisor is nought has an arm no run takes.
 *
 * <p>A fork both of whose arms nothing reaches for one reason is one report, since a report of an
 * arm points at the fork it is an arm of. Each is shown beside a control the same but for one value,
 * where a run does get there.
 */
class AnArmIsEnteredOnlyPastWhatItsForkWorksOutTest {

    private static final String GREATEST = "9223372036854775807";

    private static final String BELOW_THE_GREATEST = "9223372036854775806";

    private static String body(String lines) {
        return """
                module probe

                data Ok
                data No
                data Answer = Ok | No

                behavior f : (a: Int, b: Int) -> Answer
                let f (a, b) = {
                %s
                }
                """.formatted(lines);
    }

    /** What each of {@code reports} says and points at, for a failure to show. */
    private static String said(List<Diagnostic> reports) {
        return reports.stream().map(each -> each.primary() + " " + each.secondary().stream()
                .map(label -> label.said().toString()).toList()).toList().toString();
    }

    /** The reports that nothing reaches an arm. */
    private static List<Diagnostic> deadBranches(String source) {
        return Compiler.compileWithWarnings(source).warnings().stream()
                .filter(each -> each.code().equals("E1327"))
                .toList();
    }

    /** Whether {@code report} points at something the way there has to get past. */
    private static boolean pointsAtAnAnswer(Diagnostic report) {
        return report.secondary().stream().map(LabeledRegion::said)
                .anyMatch(DeadBranchMessage.ThisHasToAnswerOnTheWayHere.class::isInstance);
    }

    @Test
    void neitherArmOfAForkOnASumNoRunGetsPastIsEntered() {
        List<Diagnostic> dead = deadBranches(body("""
                    guard a == %s else No
                    if a + 1 > b then Ok else No""".formatted(GREATEST)));
        assertEquals(1, dead.size(), said(dead));
        assertTrue(pointsAtAnAnswer(dead.getFirst()), said(dead));
        assertEquals(List.of(), deadBranches(body("""
                    guard a == %s else No
                    if a + 1 > b then Ok else No""".formatted(BELOW_THE_GREATEST))));
    }

    /** And a fork past a sum no run gets past, though the fork decides on something else. */
    @Test
    void neitherArmOfAForkPastASumNoRunGetsPastIsEntered() {
        List<Diagnostic> dead = deadBranches(body("""
                    guard a == %s else No
                    let c = a + 1
                    if b > 3 then (if b > 5 then Ok else No) else No""".formatted(GREATEST)));
        assertEquals(1, dead.size(), "the fork past the sum, and not the one inside it again: "
                + said(dead));
        assertTrue(pointsAtAnAnswer(dead.getFirst()), said(dead));
        assertEquals(List.of(), deadBranches(body("""
                    guard a == %s else No
                    let c = a + 1
                    if b > 3 then (if b > 5 then Ok else No) else No"""
                .formatted(BELOW_THE_GREATEST))));
    }

    /**
     * Where every way out of a fork stops at a sum, no run leaves it, and a fork after it is
     * entered by none: why is what each way stopped at, together.
     */
    @Test
    void aForkAfterOneEveryWayOutOfWhichStopsIsEnteredByNoRun() {
        List<Diagnostic> dead = deadBranches(body("""
                    guard a == %s else No
                    let c = if b > 0 then a + 1 else a + 2
                    if b > 3 then Ok else No""".formatted(GREATEST)));
        assertEquals(1, dead.size(), said(dead));
        assertEquals(2, dead.getFirst().secondary().stream().map(LabeledRegion::said)
                        .filter(DeadBranchMessage.ThisHasToAnswerOnTheWayHere.class::isInstance)
                        .count(),
                "each way out, and what it stopped at: " + said(dead));
        assertEquals(List.of(), deadBranches(body("""
                    guard a == %s else No
                    let c = if b > 0 then a + 1 else a - 1
                    if b > 3 then Ok else No""".formatted(GREATEST))),
                "one way out answers, so a run leaves the fork by it");
    }

    @Test
    void pastAQuotientItsDivisorIsNotNought() {
        List<Diagnostic> dead = deadBranches(body("""
                    let q = 10 / b
                    if b == 0 then No else Ok"""));
        assertEquals(1, dead.size(), said(dead));
        assertTrue(pointsAtAnAnswer(dead.getFirst()), said(dead));
        assertEquals(List.of(), deadBranches(body("""
                    let q = 10 / a
                    if b == 0 then No else Ok""")));
    }
}
