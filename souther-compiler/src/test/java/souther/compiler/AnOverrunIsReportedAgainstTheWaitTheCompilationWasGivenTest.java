package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.HumanRenderer;
import souther.compiler.query.Adequacy;

import org.junit.jupiter.api.Test;

import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The wait a report quotes is the one this compilation was given.
 *
 * <p>A report about work that did not come back says how long it was given. Where that number comes
 * from used to depend on who ran the row: an arrangement said outright answered for the wait as it
 * answered for everything else, so a test that stated "this row does not come back" also stated,
 * without meaning to, a wait no compilation had been told about — and the rendered line quoted it.
 * The wait is a term, the arrangement is not, and a term the compile stated is the only thing a
 * report may quote for it.
 *
 * <p>Two waits and not one. A single expected number is met by an arrangement that invents its own
 * and by one that keeps what it was handed, and only the first of those is the defect. What this
 * asks is that the number moves when the compilation's term does.
 */
class AnOverrunIsReportedAgainstTheWaitTheCompilationWasGivenTest {

    private static final String DOES_NOT_ANSWER = """
            module example.waits
            data N = Int
            data Out = Int
            behavior run : (n: N) -> Out constructs Out
            let run (n) = Out(n.value)
            example run
              | "answers": (N(1)) -> Out(1)
            """;

    @Test
    void theQuotedWaitIsTheOneTheCompilationWasGiven() {
        assertTrue(reportedFor(Duration.ofMillis(4_321)).contains("4321ms"),
                reportedFor(Duration.ofMillis(4_321)));
        assertTrue(reportedFor(Duration.ofMillis(8_765)).contains("8765ms"),
                reportedFor(Duration.ofMillis(8_765)));
    }

    /** And nothing else is: a number from the arrangement would still be in the line beside it. */
    @Test
    void andNoOtherWaitIsInTheLine() {
        String said = reportedFor(Duration.ofMillis(4_321));

        assertEquals(List.of("4321ms"), millisecondsIn(said), said);
    }

    /** What the compile says about a row that did not come back, given {@code wait} and an
     *  arrangement under which that row does not come back. */
    private static String reportedFor(Duration wait) {
        CompileException raised = assertThrows(CompileException.class,
                () -> Compiler.compiled(DOES_NOT_ANSWER, "Main", new ArrayList<>(),
                        Adequacy.Asked.NOTHING, wait,
                        DoesNotComeBack.overrunningOn(DoesNotComeBack.everyRowOf("run"))));

        assertEquals("E1923", raised.code(), "the row did not answer");
        Diagnostic one = raised.diagnostics().get(0);
        return new HumanRenderer(false).render(one, null, Locale.ENGLISH);
    }

    /** Every number of milliseconds the rendered line says, in the order it says them. */
    private static List<String> millisecondsIn(String rendered) {
        List<String> said = new ArrayList<>();
        java.util.regex.Matcher matched =
                java.util.regex.Pattern.compile("\\d+ms").matcher(rendered);
        while (matched.find()) {
            said.add(matched.group());
        }
        return said;
    }
}
