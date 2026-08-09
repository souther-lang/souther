package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A module with two helpers to complain about complains about the earlier one first.
 *
 * <p>The helpers are checked one after another and the first one wrong is what the author is told
 * about, so which one that is comes from the order the table holds them in — and the order the table
 * holds them in should be the order they were written. An author reads their file from the top; a
 * report about the last of eight helpers, when the first is wrong the same way, sends them to the
 * wrong end of it.
 *
 * <p>Nothing about a helper table makes this true. A table built for lookup keeps whatever order its
 * hashing gives it, and the two orders agree often enough that a reordering shows up as a report
 * moving rather than as anything failing. So it is stated here, with a helper at each end of the
 * module wrong the same way.
 */
class AModuleIsToldAboutItsHelpersInTheOrderItWroteThemTest {

    /**
     * Eight helpers, of which the first and the last say nothing about what they take and have a body
     * that settles nothing either. A helper is typed by its body and never by its call sites
     * (ADR-0066), so each of those two has to be annotated and neither is. The six between them are
     * written correctly and are there to put the two ends far apart.
     */
    private static final String BOTH_ENDS_WRONG = """
            module demo

            data In = { n: Int }
            data Out = { n: Int }

            let alpha (n) = n
            let bravo (n: Int) : Int = n + 1
            let charlie (n: Int) : Int = n + 2
            let delta (n: Int) : Int = n + 3
            let echo (n: Int) : Int = n + 4
            let foxtrot (n: Int) : Int = n + 5
            let golf (n: Int) : Int = n + 6
            let zulu (n) = n

            behavior go : (i: In) -> Out
                constructs Out
            let go (i) = Out { n = alpha(i.n) + zulu(i.n) }
            """;

    private static final String ALPHA_ANNOTATED = "let alpha (n: Int) : Int = n";
    private static final String ZULU_ANNOTATED = "let zulu (n: Int) : Int = n";

    private static List<Diagnostic> refusalsFor(String source) {
        return assertThrows(CompileException.class, () -> Compiler.compile(source)).diagnostics();
    }

    /** What each report quotes, so a failure message says which helper was named. */
    private static List<List<Object>> quoted(List<Diagnostic> found) {
        return found.stream().map(d -> List.of(d.args())).toList();
    }

    private static boolean names(List<Diagnostic> found, String helper) {
        return found.stream().anyMatch(d -> d.values().containsValue(helper));
    }

    @Test
    void theEarlierOfTwoHelpersWrongTheSameWayIsTheOneReported() {
        List<Diagnostic> found = refusalsFor(BOTH_ENDS_WRONG);

        assertTrue(names(found, "alpha"),
                "the first helper written is the one reported: " + quoted(found));
        assertFalse(names(found, "zulu"),
                "and the last is not, because the first stopped the check: " + quoted(found));
    }

    /**
     * The same module with only the last helper wrong. Without this the test above would pass on a
     * table that never reached the far end at all.
     */
    @Test
    void theLastOneIsReportedWhenItIsTheOnlyOneWrong() {
        List<Diagnostic> found =
                refusalsFor(BOTH_ENDS_WRONG.replace("let alpha (n) = n", ALPHA_ANNOTATED));

        assertTrue(names(found, "zulu"),
                "the one that is wrong is the one reported: " + quoted(found));
    }

    @Test
    void allEightCompileWhenNoneOfThemIsWrong() {
        String none = BOTH_ENDS_WRONG
                .replace("let alpha (n) = n", ALPHA_ANNOTATED)
                .replace("let zulu (n) = n", ZULU_ANNOTATED);

        assertFalse(Compiler.compile(none).isEmpty(), "the module compiles");
    }
}
