package souther.compiler;

import souther.compiler.observe.ArmObservation;
import souther.compiler.source.SourceId;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Located;
import souther.compiler.execute.jvm.JvmExampleDeadlines;
import souther.compiler.observe.FailurePhase;
import souther.compiler.observe.RowOutcome;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Everything an evaluation ends with is classified where it arrives, not where it happened.
 *
 * <p>Every failure an evaluation produces comes back through one place — the worker hands it over and
 * the caller reads it there. Classifying somewhere earlier instead covers only the routes that pass
 * through that earlier place: converting a stack overflow at a reflection boundary catches the ones
 * thrown by a helper and by the behavior, and leaves the ones thrown by a generated decoder, an
 * encoder, or the reader's own walk to arrive unrecognised — where they become a compiler failure
 * rather than a report about the row.
 *
 * <p>The routes are stated rather than written as models. A stack that runs out inside a decoder
 * needs a fixture nested deeper than the parser will read, so there is no model that reaches it; what
 * is under test is the classification, and it is the classification that is asked.
 */
class WhatComesBackFromAnEvaluationIsClassifiedWhereItArrivesTest {

    private static final String COMES_BACK = """
            module example.arrives
            data N = Int
            data Out = Int
            behavior run : (n: N) -> Out constructs Out
            let run (n) = Out(n.value)
            example run
              | "answers": (N(1)) -> Out(1)
            """;

    private static final String WITH_A_TABLE = """
            module example.arrives

            data N = Int
            data Found = { n: N }
            data Missing = { why: String }

            behavior find : (n: N) -> Found | Missing

            behavior run : (n: N) -> Found | Missing
                depends on find

            let run (n, find) = find(n)

            example find
                | "one" : (N(1)) -> Found { n = N(1) }

            fake find
                | (N(1)) -> Missing { why = "none" }
            """;

    private static RowOutcome onlyRowOf(JvmExampleDeadlines arrangement) {
        Compilation compilation = Compilation.ofSource(COMES_BACK, "Main");
        compilation.withJvmExampleDeadlines(arrangement);
        compilation.answerEverything();
        SourceId sourceId = compilation.exampleSourcesOf("example.arrives").getFirst();
        List<RowOutcome> rows = compilation.db()
                .ask(new Output.Examples("example.arrives", sourceId, ArmObservation.OMIT))
                .value().rows();
        assertEquals(1, rows.size(), rows.toString());
        return rows.get(0);
    }

    /**
     * A stack overflow arriving with no reflection boundary behind it is still a stack overflow.
     *
     * <p>Before, only a {@code StackExhaustedException} — which is what the two reflection boundaries
     * make of one — was recognised, so this fell through to the arm that means the compiler is broken
     * and came out as an internal failure with no position and nothing an author could act on.
     */
    @Test
    void aStackOverflowWithNoBoundaryBehindItIsReportedAsOne() {
        RowOutcome row = onlyRowOf(DoesNotComeBack.throwingOn(
                DoesNotComeBack.everyRowOf("run"), new StackOverflowError()));

        assertEquals(FailurePhase.STACK_EXHAUSTED, row.failurePhase());
    }

    /** And it is E1924 — the settings are wrong for this model — rather than E1910. */
    @Test
    void aStackOverflowIsNotReportedAsNonTermination() {
        CompileException raised = assertThrows(CompileException.class,
                () -> Compiler.compiled(COMES_BACK, "Main", new ArrayList<>(),
                        Adequacy.Asked.NOTHING, null,
                        DoesNotComeBack.throwingOn(DoesNotComeBack.everyRowOf("run"),
                                new StackOverflowError())));

        assertEquals("E1924", raised.code());
    }

    /**
     * The reading of a written statement classifies it too, rather than rethrowing it.
     *
     * <p>An {@code Error} let past there is not a report about the fake at all: it leaves the
     * compilation as a failure of the compiler, so a table that overflowed the stack took the build
     * down instead of saying what it could not check.
     */
    @Test
    void aStackOverflowReadingATableIsSaidAtTheFake() {
        List<Located> warnings = new ArrayList<>();
        Compiler.compiledModules(List.of(WITH_A_TABLE), souther.compiler.meta.ModulePath.EMPTY,
                warnings, Adequacy.Asked.NOTHING, null,
                DoesNotComeBack.throwingOn(DoesNotComeBack.everyTableOf("find"),
                        new StackOverflowError()));

        List<String> codes = new ArrayList<>();
        for (Located said : warnings) {
            codes.add(said.diagnostic().code());
        }
        assertTrue(codes.contains("E1920") || codes.contains("E1921"),
                "the fake says what it could not check: " + codes);
    }
}
