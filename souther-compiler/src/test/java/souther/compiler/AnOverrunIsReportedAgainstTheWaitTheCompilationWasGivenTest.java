package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Note;
import souther.compiler.diag.msg.ExampleMessage;
import souther.compiler.query.Adequacy;

import org.junit.jupiter.api.Test;

import java.time.Duration;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

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
        assertEquals(new ExampleMessage.TheEvaluationDidNotAnswer("4321"),
                reportedFor(Duration.ofMillis(4_321)).said());
        assertEquals(new ExampleMessage.TheEvaluationDidNotAnswer("8765"),
                reportedFor(Duration.ofMillis(8_765)).said());
    }

    /**
     * A wait shorter than a millisecond is quoted as the wait it was.
     *
     * <p>The policy takes any positive length, so this is a wait a compilation can be given, and the
     * whole way from what it was told to what a reader sees is one length. Written as a number of
     * milliseconds anywhere along it, this arrives as none — and a run given no time at all is a
     * different thing, and one the policy refuses outright.
     */
    @Test
    void aWaitShorterThanAMillisecondIsNotQuotedAsNone() {
        assertEquals(new ExampleMessage.TheEvaluationDidNotAnswer("0.0015"),
                reportedFor(Duration.ofNanos(1_500)).said());
    }

    /**
     * And it is the only wait the report names.
     *
     * <p>The whole of what the diagnostic says, as values. A wait the arrangement invented would be
     * a second one somewhere in them, and the hint names none — so what a reader sees can quote one
     * wait and no other, whatever a catalog entry is worded like.
     */
    @Test
    void andNoOtherWaitIsAmongWhatItSays() {
        Diagnostic one = reportedFor(Duration.ofMillis(4_321));

        assertEquals(new ExampleMessage.TheEvaluationDidNotAnswer("4321"), one.said());
        assertEquals(List.of(new ExampleMessage.NotAnsweringIsNotNotTerminating()),
                one.notes().stream().map(Note::said).toList());
    }

    /** What the compile says about a row that did not come back, given {@code wait} and an
     *  arrangement under which that row does not come back. */
    private static Diagnostic reportedFor(Duration wait) {
        CompileException raised = assertThrows(CompileException.class,
                () -> Compiler.compiled(DOES_NOT_ANSWER, "Main", new ArrayList<>(),
                        Adequacy.Asked.NOTHING, wait,
                        DoesNotComeBack.overrunningOn(DoesNotComeBack.everyRowOf("run"))));

        assertEquals("E1923", raised.code(), "the row did not answer");
        return raised.diagnostics().get(0);
    }
}
