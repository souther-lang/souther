package souther.compiler;

import souther.compiler.observe.ArmObservation;
import souther.compiler.source.SourceId;

import souther.compiler.examples.EvaluationPolicy;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.FailurePhase;
import souther.compiler.observe.RowOutcome;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * How deep a recursion may go is this compile's answer, not the JVM's.
 *
 * <p>A recursion that does not stop runs out of stack, and how many frames a stack holds depends on
 * how big the frames are — which depends on the helper, and on whether the JVM has compiled it yet.
 * So a model whose depth is decided that way compiles under one {@code -Xss} and is reported as
 * non-terminating under another, which is the same defect the wall clock has in a different place.
 * Counting the frames answers the same everywhere.
 */
class ARecursionIsHeldToItsDepthAndNotToTheStackTest {

    /** A helper that recurses without a tail call, so each call really is a frame: the addition after
     *  the call is what stops the emitter turning it into a loop. */
    private static String countingDownFrom(long depth) {
        return """
                module example.deep
                data N = Int
                data Out = Int
                partial let count (n: Int): Int = if n == 0 then 0 else count(n - 1) + 1
                behavior run : (n: N) -> Out constructs Out
                let run (n) = Out(count(n.value))
                example run
                  | "counts down": (N(%d)) -> Out(%d)
                """.formatted(depth, depth);
    }

    /** The same recursion, carrying eight parameters it does not need, so each frame is larger. */
    private static String carryingEightMore(long depth) {
        return """
                module example.deep
                data N = Int
                data Out = Int
                partial let count (n: Int, a: Int, b: Int, c: Int, d: Int, e: Int, f: Int,
                                   g: Int): Int =
                    if n == 0 then 0 else count(n - 1, a, b, c, d, e, f, g) + 1
                behavior run : (n: N) -> Out constructs Out
                let run (n) = Out(count(n.value, 1, 2, 3, 4, 5, 6, 7))
                example run
                  | "counts down": (N(%d)) -> Out(%d)
                """.formatted(depth, depth);
    }

    private static RowOutcome onlyRowOf(String source, EvaluationPolicy policy) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.withEvaluationPolicy(policy);
        compilation.answerEverything();
        SourceId sourceId = compilation.exampleSourcesOf("example.deep").getFirst();
        List<RowOutcome> rows =
                compilation.db().ask(new Output.Examples("example.deep", sourceId, ArmObservation.OMIT)).value().rows();
        assertEquals(1, rows.size(), rows.toString());
        return rows.get(0);
    }

    /** A recursion that goes deeper than the policy allows is reported for its depth, and told apart
     *  from one that spent its steps: what an author does about the two is not the same. */
    @Test
    void aRecursionDeeperThanTheLimitIsReportedForItsDepth() {
        RowOutcome row = onlyRowOf(countingDownFrom(5_000),
                EvaluationPolicy.DEFAULT.withRecursionDepthLimit(100));

        assertEquals(Disposition.INCOMPLETE, row.disposition());
        assertEquals(FailurePhase.DEPTH_LIMIT, row.failurePhase());
    }

    /** And one that stays within it comes back, on the same policy. */
    @Test
    void aRecursionWithinTheLimitComesBack() {
        RowOutcome row = onlyRowOf(countingDownFrom(90),
                EvaluationPolicy.DEFAULT.withRecursionDepthLimit(100));

        assertEquals(Disposition.HELD, row.disposition());
    }

    /**
     * On the policy a build runs under, the counted limit is what a runaway recursion reaches.
     *
     * <p>This is the relation the two settings are chosen for: the stack an evaluation is given has to
     * hold more frames than the depth limit allows, or the JVM answers first and the answer stops
     * being this compile's. It cannot be proven — a frame's size is the helper's business — so it is
     * asserted on a recursion far deeper than the limit instead.
     */
    @Test
    void theCountedLimitIsReachedBeforeTheStackRunsOut() {
        RowOutcome row = onlyRowOf(
                countingDownFrom(EvaluationPolicy.DEFAULT_RECURSION_DEPTH_LIMIT * 2L),
                EvaluationPolicy.DEFAULT);

        assertEquals(FailurePhase.DEPTH_LIMIT, row.failurePhase());
    }

    /**
     * And for a helper whose frames are large, which is the case that decides where the limit can be.
     *
     * <p>A recursion carrying eight more parameters than it needs takes more stack per frame, so the
     * stack holds fewer of them — and the counted limit still has to be the one that answers. The
     * plain helper above would pass at a depth setting far too high for this one.
     */
    @Test
    void theCountedLimitIsReachedFirstForAHelperWithWideFramesToo() {
        RowOutcome row = onlyRowOf(
                carryingEightMore(EvaluationPolicy.DEFAULT_RECURSION_DEPTH_LIMIT * 2L),
                EvaluationPolicy.DEFAULT);

        assertEquals(FailurePhase.DEPTH_LIMIT, row.failurePhase());
    }
}
