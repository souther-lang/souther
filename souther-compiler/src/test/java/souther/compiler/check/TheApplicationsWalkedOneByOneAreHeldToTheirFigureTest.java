package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.Compiler;

import java.util.Collections;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The applications one reading of a body walks one at a time are held to
 * {@link PathReachability#APPLICATIONS_WALKED_ONE_BY_ONE} across every call in it, and one past
 * the figure is taken as one nothing has shown no run gets past: the branch after it is not
 * reported as one nothing reaches.
 *
 * <p>Two calls, so that the figure is reached by what they walk together and not by a list
 * longer than any the reading writes out. The first gets past every application; the second stops
 * on its last. With the figure walked to exactly, that last application is walked and the branch
 * after the calls is reported; with one element more in the first list, it is not.
 */
class TheApplicationsWalkedOneByOneAreHeldToTheirFigureTest {

    private static final String GREATEST = "9223372036854775807";

    /** Whether nothing reaches a branch after a first call over {@code passing} elements no
     *  application stops on, and a second over two whose second stops every run. */
    private static boolean aBranchIsReportedDead(int passing) {
        String zeros = String.join(", ", Collections.nCopies(passing, "0"));
        return Compiler.compileWithWarnings("""
                module probe

                data Ok
                data No
                data Answer = Ok | No

                behavior f : (n: Int, d: Date, b: Int) -> Answer
                let f (n, d, b) = {
                    guard n == %s else No
                    let xs = List.map(k -> Date.addDays(k * n, d), [%s])
                    let ys = List.map(k -> Date.addDays(k * n, d), [0, 1])
                    if b > 3 then Ok else No
                }
                """.formatted(GREATEST, zeros)).warnings().stream()
                .anyMatch(each -> each.code().equals("E1327"));
    }

    @Test
    void theLastApplicationTheFigureAllowsIsWalked() {
        assertTrue(aBranchIsReportedDead(PathReachability.APPLICATIONS_WALKED_ONE_BY_ONE - 2));
    }

    @Test
    void anApplicationPastTheFigureIsNotWalked() {
        assertFalse(aBranchIsReportedDead(PathReachability.APPLICATIONS_WALKED_ONE_BY_ONE - 1));
    }
}
