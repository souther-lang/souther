package souther.compiler;

import souther.compiler.examples.EvaluationPolicy;
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
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A dependency's code is counted, whether it travelled as source or stayed in its jar.
 *
 * <p>A published module carries what an importer needs to read its declarations — its types, its
 * invariants, the {@code let}s it exposes — and a behavior's body stays in the jar it was built into.
 * Regenerating what travels and taking the rest from the jar is the one thing that cannot be done: a
 * class defined by the evaluation's loader and one defined by the parent are different types under
 * one binary name, so a module split between them hands its own types to its own implementation and
 * the cast fails, reported as an example that does not hold about a model that is fine.
 *
 * <p>So a module from the path is not regenerated at all. Its classes are taken whole and given a
 * counted point on every backward branch as the evaluation loads them, which is one loader, one
 * version of every type, and a budget that does not stop at the import.
 *
 * <p>What rewriting cannot add is the recursion-depth count, which the emitter puts in by moving a
 * helper's body aside and wrapping it. A recursion inside a jar is bounded by the stack the
 * evaluation runs on and reported as having exhausted it.
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
     * loaded as they were built, the loop inside them would have no counted point in it and the row
     * would run until the wait ran out instead — reported as the compiler failing to answer, on a
     * model whose fault is plain.
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

    /**
     * A behavior's body, which stays in the jar, is counted too.
     *
     * <p>This is the case the counting used to stop at, and it stopped badly. The dependency's types
     * were regenerated here and its body was not, so the row handed this loader's types to the jar's
     * implementation and the cast failed — and what came out was "this example does not hold", about
     * a model whose dependency loops forever.
     */
    @Test
    void aBehaviorBodyThatStaysInTheJarIsCountedToo() {
        Map<String, byte[]> jar = Compiler.compile("""
                module lib.svc exposing ( Amount, spin )

                data Amount = Int

                behavior spin : (a: Amount) -> Amount
                    constructs Amount

                partial let forever (n: Int): Int = forever(n)

                let spin (a) = Amount(forever(a.value))
                """);
        Compilation compilation = Compilation.ofSources(List.of("""
                module app.calls
                import lib.svc ( Amount, spin )

                data Receipt = { total: Amount }

                behavior bill : (a: Amount) -> Receipt
                    constructs Receipt

                let bill (a) = Receipt { total = spin(a) }

                example bill
                  | "reaches the dependency body": (Amount(1)) -> Receipt { total = Amount(0) }
                """), jar::get);
        compilation.withEvaluationPolicy(EvaluationPolicy.of(50_000L));
        compilation.answerEverything();

        assertFalse(compilation.db()
                        .ask(new Output.EvaluationLinked("app.calls", Output.CoverageMode.NONE))
                        .value().containsKey("lib.svc.Spin$Impl"),
                "the body is not regenerated here — it is taken from the jar and counted there");

        String sourceId = compilation.exampleSourcesOf("app.calls").get(0);
        List<RowOutcome> rows = compilation.db()
                .ask(new Output.Examples("app.calls", sourceId, Output.CoverageMode.NONE))
                .value().rows();

        assertEquals(FailurePhase.STEP_LIMIT, rows.get(0).failurePhase(),
                "the row spent its budget inside the jar's body: " + rows);
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

        assertNull(compilation.failure(compilation.db().allReports()));
        assertTrue(compilation.db()
                        .ask(new Output.EvaluationLinked("app.alone", Output.CoverageMode.NONE))
                        .value() != null,
                "nothing on the path is not a class this compile failed to produce");
    }
}
