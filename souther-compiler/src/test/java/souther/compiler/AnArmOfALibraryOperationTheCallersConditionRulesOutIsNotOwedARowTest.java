package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A condition inside a copy of a library operation is no rule of the model, and it still decides
 * which of that operation's arms a run can get to.
 *
 * <p>{@code Int.abs} is called only where the caller has already found {@code left} negative, so
 * the arm that answers an argument that is not negative is one no row can go through, and no row
 * is owed there.
 */
class AnArmOfALibraryOperationTheCallersConditionRulesOutIsNotOwedARowTest {

    private static final String GUARDED = """
            module p
            data Late = { over: Int }
            behavior f : (left: Int) -> Int | Late
            let f (left) = {
                guard left >= 0 else Late { over = Int.abs(left) }
                left
            }
            example f
                | (3) -> 3
                | (0) -> 0
                | (-2) -> Late { over = 2 }
            """;

    private static final String IF_FORM = """
            module p
            behavior f : (left: Int) -> Int
            let f (left) = if left < 0 then Int.abs(left) else left
            example f
                | (3) -> 3
                | (0) -> 0
                | (-2) -> 2
            """;

    private static final String MAX_FORM = """
            module p
            behavior f : (left: Int) -> Int
            let f (left) = if left < 0 then Int.max(left, 0 - left) else left
            example f
                | (3) -> 3
                | (0) -> 0
                | (-2) -> 2
            """;

    /** Nothing says the argument is negative, so both arms of {@code abs} are owed a row. */
    private static final String UNCONDITIONAL = """
            module p
            behavior f : (x: Int) -> Int
            let f (x) = Int.abs(x)
            example f
                | (3) -> 3
                | (0) -> 0
            """;

    @Test
    void anArmTheGuardRulesOutIsNotAGap() {
        assertFalse(report(GUARDED).contains("no row goes through"), () -> report(GUARDED));
    }

    @Test
    void anArmTheIfRulesOutIsNotAGap() {
        assertFalse(report(IF_FORM).contains("no row goes through"), () -> report(IF_FORM));
    }

    @Test
    void anArmOfMaxTheIfRulesOutIsNotAGap() {
        assertFalse(report(MAX_FORM).contains("no row goes through"), () -> report(MAX_FORM));
    }

    @Test
    void anArmNothingRulesOutIsStillOwed() {
        assertTrue(report(UNCONDITIONAL).contains("no row goes through"),
                () -> report(UNCONDITIONAL));
    }

    private static String report(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }
}
