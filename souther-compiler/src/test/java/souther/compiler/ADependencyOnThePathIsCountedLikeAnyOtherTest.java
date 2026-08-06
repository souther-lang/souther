package souther.compiler;

import souther.compiler.meta.ModulePath;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.FailurePhase;
import souther.compiler.observe.RowOutcome;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;

import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A module compiled by another project is counted like one compiled here.
 *
 * <p>A published module travels as the source it was written as, so asking this compilation for its
 * classes asks for the same generation any source module gets — including the counting. A row that
 * steps into a dependency is therefore still held to the budget while it is in there, which is what
 * stops the counting from ending at the first import.
 *
 * <p>The other half is that a dependency must not be treated as a class this compile failed to
 * produce. A set of evaluation classes is whole or absent for the modules this compilation declares;
 * a module that came from the path is on the loader that set is put over, so leaving it out costs the
 * counting and nothing else. Refusing instead would stop evaluating the rows of every module that
 * imports a dependency, which is every model of any size.
 */
class ADependencyOnThePathIsCountedLikeAnyOtherTest {

    /** Published by another project: it exposes a type and a helper that does not stop. */
    private static final String PUBLISHED = """
            module lib.spin exposing ( Amount, spun )
            data Amount = Int
            partial let spun (n: Int): Int = spun(n)
            """;

    private static ModulePath published() {
        Map<String, byte[]> classes = Compiler.compile(PUBLISHED);
        return classes::get;
    }

    private static RowOutcome onlyRowOf(String source, EvaluationPolicy policy) {
        Compilation compilation = Compilation.ofSources(List.of(source), published());
        compilation.withEvaluationPolicy(policy);
        compilation.answerEverything();
        String sourceId = compilation.exampleSourcesOf("app.uses").get(0);
        List<RowOutcome> rows = compilation.db()
                .ask(new Output.Examples("app.uses", sourceId, Output.CoverageMode.NONE))
                .value().rows();
        assertEquals(1, rows.size(), rows.toString());
        return rows.get(0);
    }

    /** A row that only reaches the dependency's types runs, and holds. */
    @Test
    void aRowThatImportsFromThePathIsEvaluated() {
        RowOutcome row = onlyRowOf("""
                module app.uses
                import lib.spin ( Amount )

                data Receipt = { total: Amount }

                behavior bill : (a: Amount) -> Receipt
                    constructs Receipt

                let bill (a) = Receipt { total = a }

                example bill
                  | "passes it through": (Amount(5)) -> Receipt { total = Amount(5) }
                """, EvaluationPolicy.DEFAULT);

        assertEquals(Disposition.HELD, row.disposition());
    }

    /**
     * And a row that steps into the dependency's looping helper is stopped by the budget there.
     *
     * <p>This is what says the counting did not end at the import. Were the dependency's classes
     * taken from the path as they were built, the loop inside them would have no counted point in it
     * and the row would run until the wait ran out instead — reported as the compiler failing to
     * answer, on a model whose fault is plain.
     */
    @Test
    void aRowThatLoopsInsideThePathModuleSpendsItsBudgetThere() {
        RowOutcome row = onlyRowOf("""
                module app.uses
                import lib.spin ( Amount, spun )

                data Receipt = { total: Amount }

                behavior bill : (a: Amount) -> Receipt
                    constructs Receipt, Amount

                let bill (a) = Receipt { total = Amount(spun(a.value)) }

                example bill
                  | "loops in the dependency": (Amount(1)) -> Receipt { total = Amount(0) }
                """, EvaluationPolicy.of(50_000L));

        assertEquals(FailurePhase.STEP_LIMIT, row.failurePhase());
        assertEquals(50_000L, row.stepsSpent(), "it spent the budget inside the dependency");
    }

    /** A dependency this compiler cannot read at all leaves the rows to run against whatever the
     *  loader has, rather than refusing to evaluate them. */
    @Test
    void aDependencyThatCannotBeRegeneratedDoesNotMakeTheSetAbsent() {
        Compilation compilation = Compilation.ofSources(List.of("""
                module app.alone
                data N = Int
                data Out = Int
                behavior run : (n: N) -> Out constructs Out
                let run (n) = Out(n.value)
                example run
                  | "answers": (N(1)) -> Out(1)
                """), name -> null);
        compilation.answerEverything();

        assertNull(compilation.firstError(compilation.db().allReports()));
        assertTrue(compilation.db()
                        .ask(new Output.EvaluationLinked("app.alone", Output.CoverageMode.NONE))
                        .value() != null,
                "nothing on the path is not a class this compile failed to produce");
    }
}
