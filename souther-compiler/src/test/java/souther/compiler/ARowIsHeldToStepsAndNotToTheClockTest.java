package souther.compiler;

import souther.compiler.source.SourceId;

import souther.compiler.examples.EvaluationPolicy;
import souther.compiler.diag.CompileException;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.FailurePhase;
import souther.compiler.observe.Counting;
import souther.compiler.observe.RowOutcome;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;

import org.junit.jupiter.api.Test;

import java.time.Duration;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What stops a row that does not come back is a budget it spends, not a clock it loses to.
 *
 * <p>A wall clock makes whether a model compiles a property of the host: the same row is reported as
 * one that did not terminate on a loaded machine and passes on a quiet one, so a model that compiles
 * here need not compile there. Counting what the generated code goes through answers the same on
 * every machine.
 *
 * <p>These read the outcome the row left rather than the sentence written about it: what has to be
 * the same everywhere is which of the two things happened, and a test that matched on the wording
 * would still pass if the two were confused with each other.
 */
class ARowIsHeldToStepsAndNotToTheClockTest {

    /** A row whose helper tail-calls itself with the same argument: the emitter compiles that to a
     *  loop, so it goes round forever without ever growing the stack. */
    private static final String LOOPS = """
            module example.loops
            data N = Int
            data Out = Int
            partial let spin (n: Int): Int = spin(n)
            behavior run : (n: N) -> Out constructs Out
            let run (n) = Out(spin(n.value))
            example run
              | "loops": (N(1)) -> Out(0)
            """;

    /** A row that comes back after doing a bounded amount of work. */
    private static final String COUNTS_DOWN = """
            module example.loops
            data N = Int
            data Out = Int
            partial let spin (n: Int): Int = if n == 0 then 0 else spin(n - 1)
            behavior run : (n: N) -> Out constructs Out
            let run (n) = Out(spin(n.value))
            example run
              | "counts down": (N(1000)) -> Out(0)
            """;

    /** Steps enough for anything these models do that finishes, and a clock long enough that losing
     *  to it would be a test that hangs rather than one that fails. */
    private static EvaluationPolicy holdingTo(long steps) {
        return EvaluationPolicy.of(steps).withOuterTimeout(Duration.ofSeconds(30));
    }

    private static Compilation compiled(String source, EvaluationPolicy policy) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.withEvaluationPolicy(policy);
        compilation.answerEverything();
        return compilation;
    }

    private static RowOutcome onlyRowOf(Compilation compilation, String module) {
        SourceId sourceId = compilation.exampleSourcesOf(module).getFirst();
        List<RowOutcome> rows =
                compilation.db().ask(new Output.Examples(module, sourceId, Output.CoverageMode.NONE)).value().rows();
        assertEquals(1, rows.size(), rows.toString());
        return rows.get(0);
    }

    /**
     * The row spends its steps and is reported for that, with a clock running that it never reaches.
     *
     * <p>The distinction the outcome carries is the point: spending a budget is something the model
     * did, and losing to a clock is something the host did.
     */
    @Test
    void aRowThatLoopsIsReportedForSpendingItsSteps() {
        RowOutcome row = onlyRowOf(compiled(LOOPS, holdingTo(10_000L)), "example.loops");

        assertEquals(Disposition.INCOMPLETE, row.disposition());
        assertEquals(FailurePhase.STEP_LIMIT, row.failurePhase());
    }

    /** And it fails the build, as a row that does not come back always has. */
    @Test
    void aRowThatSpendsItsStepsFailsTheBuild() {
        CompileException raised = assertThrows(CompileException.class,
                () -> Compiler.compiled(LOOPS, "Main", new java.util.ArrayList<>(),
                        souther.compiler.query.Adequacy.Asked.NOTHING, holdingTo(10_000L)));

        assertEquals("E1910", raised.code());
    }

    /**
     * Which rows are reported is decided by the steps allowed and by nothing else.
     *
     * <p>The same row, the same host, the same moment: given steps to spare it comes back, and given
     * fewer than it needs it does not. Nothing about how fast the machine is enters into it.
     */
    @Test
    void theSameRowIsDecidedByTheStepsItIsAllowed() {
        RowOutcome withRoom = onlyRowOf(compiled(COUNTS_DOWN, holdingTo(1_000_000L)), "example.loops");
        RowOutcome withoutRoom = onlyRowOf(compiled(COUNTS_DOWN, holdingTo(100L)), "example.loops");

        assertEquals(Disposition.HELD, withRoom.disposition());
        assertEquals(Disposition.INCOMPLETE, withoutRoom.disposition());
        assertEquals(FailurePhase.STEP_LIMIT, withoutRoom.failurePhase());
    }

    /**
     * A row that spent its budget says what it cost.
     *
     * <p>Read on the way out of the evaluation whichever way it leaves. Read only where the row came
     * back, the row most worth knowing the cost of — the one stopped by its budget — recorded nothing,
     * and said it had spent none, which is what a row that never ran says.
     */
    @Test
    void aRowThatSpendsItsStepsSaysWhatItCost() {
        RowOutcome row = onlyRowOf(compiled(LOOPS, holdingTo(10_000L)), "example.loops");

        assertEquals(10_000L, steps(row),
                "it spent what it was allowed, and that is what it reports");
    }

    /**
     * A row that spent its budget leaves nothing running.
     *
     * <p>A worker asked to stop that cannot be made to goes on burning a core for as long as the JVM
     * lives, and the rows after it are then evaluated on a machine this compile is loading. That is
     * how one row that does not come back makes the next one's reading depend on it. Code that stops
     * itself when its budget is gone leaves no such worker.
     */
    @Test
    void aRowThatSpendsItsStepsLeavesNoWorkerRunning() {
        Set<Thread> before = evaluationWorkers();

        compiled(LOOPS, holdingTo(10_000L));

        assertTrue(noWorkerRemainsBeyond(before), "an evaluation worker was left running");
    }

    /**
     * Whether every worker this test started has finished.
     *
     * <p>Only the ones it started. Every test in the suite shares a JVM, and one that overran on
     * purpose may still have a worker of its own going round — which is the very thing being tested
     * here and would answer for a compile that is not this one.
     *
     * <p>Polled rather than read once: a worker that stops itself is still scheduled off after it
     * does, and what is being asked is whether it stops, not how soon.
     */
    private static boolean noWorkerRemainsBeyond(Set<Thread> before) {
        for (int attempt = 0; attempt < 100; attempt++) {
            Set<Thread> now = new java.util.HashSet<>(evaluationWorkers());
            now.removeAll(before);
            if (now.isEmpty()) {
                return true;
            }
            try {
                Thread.sleep(20);
            } catch (InterruptedException _) {
                Thread.currentThread().interrupt();
                return false;
            }
        }
        return false;
    }

    private static Set<Thread> evaluationWorkers() {
        Set<Thread> running = new java.util.HashSet<>();
        for (Thread t : Thread.getAllStackTraces().keySet()) {
            if (t.getName().startsWith("souther-reading") && t.isAlive()) {
                running.add(t);
            }
        }
        return running;
    }

    /** What a row spent: the counted work of its whole evaluation, fixtures and application alike,
     * from a row whose counting was read. */
    private static long steps(RowOutcome row) {
        return assertInstanceOf(Counting.Read.class, row.run().counting(),
                "the row came back, so its counting was read").steps();
    }

}
