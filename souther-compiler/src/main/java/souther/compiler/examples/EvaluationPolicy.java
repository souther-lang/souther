package souther.compiler.examples;

import java.time.Duration;

/**
 * What a compile allows one row's evaluation, and what it allows the machinery running it.
 *
 * <p>The first two are what decide a row. {@code stepLimit} is how many times the evaluated code may
 * pass a point the emitter counts, and {@code recursionDepthLimit} is how deep a recursive helper may
 * go; a row that spends either is reported, and the reading is the same on every machine because
 * neither is a measure of time. Two compiles of the same model under the same policy therefore say
 * the same thing about it, however fast the host is and however loaded.
 *
 * <p>The last two are not about the model at all. {@code outerTimeout} is the wait after which the
 * evaluation is given up on, and it exists for what a counter cannot reach — a call into code this
 * compile did not generate, so has no counted points in. Losing to it is the compiler failing to
 * answer, not the model failing to terminate, and the two are reported as the different things they
 * are. {@code workerStackBytes} is the stack an evaluation runs on, said outright so that the depth a
 * recursion reaches is this compile's answer rather than whatever {@code -Xss} the JVM happens to
 * have been started with.
 *
 * <p>The relation between the two pairs is one-directional and cannot be made exact: the depth limit
 * is set to be reached before the stack runs out, and the outer timeout to be reached long after any
 * budget a row could spend. Neither can be proven — a frame's size depends on the helper it is for,
 * and a step's cost depends on what the step does — so both are set with room rather than derived.
 */
public record EvaluationPolicy(long stepLimit, int recursionDepthLimit, Duration outerTimeout,
                               long workerStackBytes) {

    /**
     * Steps enough for anything a model states as an example, and far short of what code that does
     * not stop would take.
     *
     * <p>Set from what the models this compiler is tested against actually spend, with room above the
     * heaviest of them. A row that reaches this is doing something no example does.
     */
    public static final long DEFAULT_STEP_LIMIT = 100_000_000L;

    /**
     * Deep enough for any recursion over data a row can state, and shallow enough to be reached
     * before the stack it runs on runs out.
     *
     * <p>Which of the two happens first cannot be settled by reasoning about it: a frame's size is
     * decided by the helper's parameters and locals, so the depth a given stack holds differs between
     * helpers. It was settled by measuring instead. On {@link #DEFAULT_WORKER_STACK_BYTES}, a plain
     * recursion and one carrying eight extra parameters both reach a counted limit of a hundred
     * thousand before the stack; at two hundred thousand the wide one runs the stack out first, at
     * about a hundred and fifty thousand frames.
     *
     * <p>Set below that rather than at it, and set higher than the depth any model here reaches. The
     * two ways this can be wrong are not equally bad: too low reports a legitimate deep walk as a
     * recursion that does not terminate, which is a wrong answer about the model, while too high
     * reports that the stack ran out first — which says the settings are wrong for this model and
     * what to do about it.
     */
    public static final int DEFAULT_RECURSION_DEPTH_LIMIT = 50_000;

    /**
     * How long the compiler waits before giving up on an evaluation that has stopped answering.
     *
     * <p>Generous, because reaching it is not an answer about the model: a row decided by its steps
     * is decided long before this, and a row that reaches this is one the counters could not see into.
     * A short one would turn slow-but-counted work into a failure to answer, which is the reading this
     * whole arrangement exists to stop.
     */
    public static final Duration DEFAULT_OUTER_TIMEOUT = Duration.ofSeconds(60);

    /**
     * The stack an evaluation is given.
     *
     * <p>Large, and said here rather than inherited, so that how deep a recursion gets before the
     * stack runs out is not something the surrounding JVM decides. The depth limit is what is meant to
     * stop a recursion; this is what makes room for it to, and how much room it makes is what
     * {@link #DEFAULT_RECURSION_DEPTH_LIMIT} was measured against.
     */
    public static final long DEFAULT_WORKER_STACK_BYTES = 64L * 1024 * 1024;

    /** What a compile that says nothing is held to. */
    public static final EvaluationPolicy DEFAULT = new EvaluationPolicy(DEFAULT_STEP_LIMIT,
            DEFAULT_RECURSION_DEPTH_LIMIT, DEFAULT_OUTER_TIMEOUT, DEFAULT_WORKER_STACK_BYTES);

    public EvaluationPolicy {
        if (stepLimit <= 0) {
            throw new IllegalArgumentException("a step limit has to be positive: " + stepLimit);
        }
        if (recursionDepthLimit <= 0) {
            throw new IllegalArgumentException(
                    "a recursion depth limit has to be positive: " + recursionDepthLimit);
        }
        if (outerTimeout == null || outerTimeout.isNegative() || outerTimeout.isZero()) {
            throw new IllegalArgumentException("an outer timeout has to be positive: " + outerTimeout);
        }
        if (workerStackBytes <= 0) {
            throw new IllegalArgumentException(
                    "a worker stack size has to be positive: " + workerStackBytes);
        }
    }

    /**
     * The policy this JVM's settings ask for, read now.
     *
     * <p>Read at the point a compilation is set up, and held by that compilation, rather than read
     * wherever a row happens to be evaluated. A setting read once into a static is fixed for the life
     * of the JVM, which is the wrong answer in every long-lived one: a build daemon or an editor's
     * language server outlives the compile a setting was written for, and two compiles in one JVM may
     * legitimately want different answers.
     *
     * <p>A setting that is missing, unreadable or not positive leaves that part of the default in
     * place. There is nothing useful to say about a budget written as {@code "soon"}, and refusing to
     * compile over it would make a typo in a build script look like a broken model.
     */
    public static EvaluationPolicy fromSettings() {
        return new EvaluationPolicy(
                positiveLong("souther.example.step.limit", DEFAULT_STEP_LIMIT),
                (int) Math.min(Integer.MAX_VALUE,
                        positiveLong("souther.example.recursion.depth",
                                DEFAULT_RECURSION_DEPTH_LIMIT)),
                Duration.ofMillis(positiveLong("souther.example.outer.timeout.ms",
                        DEFAULT_OUTER_TIMEOUT.toMillis())),
                positiveLong("souther.example.worker.stack.bytes", DEFAULT_WORKER_STACK_BYTES));
    }

    private static long positiveLong(String setting, long fallback) {
        String written = System.getProperty(setting);
        if (written == null) {
            return fallback;
        }
        try {
            long asked = Long.parseLong(written.trim());
            return asked > 0 ? asked : fallback;
        } catch (NumberFormatException _) {
            return fallback;
        }
    }

    /** The default, holding a row to {@code stepLimit} steps. */
    public static EvaluationPolicy of(long stepLimit) {
        return new EvaluationPolicy(stepLimit, DEFAULT_RECURSION_DEPTH_LIMIT, DEFAULT_OUTER_TIMEOUT,
                DEFAULT_WORKER_STACK_BYTES);
    }

    public EvaluationPolicy withStepLimit(long steps) {
        return new EvaluationPolicy(steps, recursionDepthLimit, outerTimeout, workerStackBytes);
    }

    public EvaluationPolicy withRecursionDepthLimit(int depth) {
        return new EvaluationPolicy(stepLimit, depth, outerTimeout, workerStackBytes);
    }

    public EvaluationPolicy withOuterTimeout(Duration timeout) {
        return new EvaluationPolicy(stepLimit, recursionDepthLimit, timeout, workerStackBytes);
    }

    public EvaluationPolicy withWorkerStackBytes(long bytes) {
        return new EvaluationPolicy(stepLimit, recursionDepthLimit, outerTimeout, bytes);
    }
}
