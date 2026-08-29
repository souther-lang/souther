package souther.compiler;

import souther.compiler.observe.ArmObservation;
import souther.compiler.source.SourceId;

import souther.compiler.diag.CompileException;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.FailurePhase;
import souther.compiler.observe.RowOutcome;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A row the compiler could not decide is reported as that, and not as a row that does not terminate.
 *
 * <p>E1910 says the model reaches something that goes round more than an example may. Two other
 * things end an evaluation and say nothing of the kind: the evaluation stops answering, and the JVM
 * runs out of stack before the counted depth limit is reached. Neither is decided by what the model
 * says — the first depends on what the host was doing, the second on how big the frames happen to be
 * — so a model they are reported against may be perfectly good, and telling an author to make a
 * recursion structural because of one of them sends them to fix something that is not wrong.
 */
class AnEvaluationThatCouldNotAnswerIsNotTheModelsFaultTest {

    private static final String COMES_BACK = """
            module example.answers
            data N = Int
            data Out = Int
            behavior run : (n: N) -> Out constructs Out
            let run (n) = Out(n.value)
            example run
              | "answers": (N(1)) -> Out(1)
            """;

    private static RowOutcome onlyRowOf(Compilation compilation) {
        SourceId sourceId = compilation.exampleSourcesOf("example.answers").getFirst();
        List<RowOutcome> rows = compilation.db()
                .ask(new Output.Examples("example.answers", sourceId, ArmObservation.OMIT))
                .value().rows();
        assertEquals(1, rows.size(), rows.toString());
        return rows.get(0);
    }

    /** A compile whose row is said not to come back, rather than written so that it does not. */
    private static Compilation whoseRowDoesNotAnswer() {
        Compilation compilation = Compilation.ofSource(COMES_BACK, "Main");
        compilation.withJvmExampleDeadlines(DoesNotComeBack.overrunningOn(DoesNotComeBack.everyRowOf("run")));
        compilation.answerEverything();
        return compilation;
    }

    /**
     * The row is recorded as one the evaluation could not decide, which is a different phase from
     * having spent a budget.
     */
    @Test
    void aRowThatDidNotAnswerIsRecordedAsUndecidedRatherThanOverspent() {
        RowOutcome row = onlyRowOf(whoseRowDoesNotAnswer());

        assertEquals(Disposition.INCOMPLETE, row.disposition());
        assertEquals(FailurePhase.TIMEOUT, row.failurePhase());
        assertNotEquals(FailurePhase.STEP_LIMIT, row.failurePhase());
    }

    /** And what it is reported as is not E1910: nothing here says the model does not terminate. */
    @Test
    void aRowThatDidNotAnswerIsNotReportedAsNonTermination() {
        CompileException raised = assertThrows(CompileException.class,
                () -> Compiler.compiled(COMES_BACK, "Main", new java.util.ArrayList<>(),
                        souther.compiler.query.Adequacy.Asked.NOTHING, null,
                        DoesNotComeBack.overrunningOn(DoesNotComeBack.everyRowOf("run"))));

        assertNotEquals("E1910", raised.code(),
                "the evaluation failed to answer; the model was not shown to loop");
        assertEquals("E1923", raised.code());
    }
}
