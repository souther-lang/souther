package souther.compiler.execute;

import java.time.Duration;

/**
 * What a compile holds one row's evaluation to, whoever runs it.
 *
 * <p>Terms and not a way of meeting them. Each of the three is a condition on the answer — how much
 * the evaluated code may spend, how deep it may go, and how long the caller may be made to wait —
 * and none of them says how an execution arranges to keep it. That is why they are here rather than
 * beside the JVM's arrangement: an execution that is not this one honours the same three by its own
 * means, and reads them without naming the subsystem that happens to run them today.
 *
 * <p>The first two are what decide a row. {@code stepLimit} is how many times the evaluated code may
 * pass a point the emitter counts, and {@code recursionDepthLimit} is how deep a recursive helper may
 * go; a row that spends either is reported, and the reading is the same on every machine because
 * neither is a measure of time. Two compiles of the same model under the same policy therefore say
 * the same thing about it, however fast the host is and however loaded.
 *
 * <p>{@code compilerTimeout} is not about the model at all. It exists for what a counter cannot
 * reach — a call into code this compile did not generate, so has no counted points in. Losing to it
 * is the compiler failing to answer, not the model failing to terminate, and the two are reported as
 * the different things they are.
 *
 * <p>What it obliges an execution to is elapsed time, and the elapsed time it obliges is the
 * compiler's own: past this, the compiler has not gone on working without answering. What decides
 * whose it is is ownership and not who wrote the code — an implementation a caller supplied is
 * answering out of the caller's world, and what that world takes is the caller's, so a clock over it
 * would report a caller's database as this compiler failing to answer. Where a run is the compiler's
 * from beginning to end, which is every run a compile makes for itself, this is the whole of the
 * wait and the caller is not still waiting past it.
 *
 * <p>A limit on how much work is done is not the same promise and does not discharge it — an
 * implementation counting fuel, instructions or reductions has bounded the work and not the wait, and
 * still owes a clock of its own. What that clock is belongs to the implementation, and so is where
 * it draws the line between its own time and the world's; that there is one, and that it is not over
 * what the caller's own code takes, is what reading this means.
 *
 * <p>The relation between the counted pair and the wait is one-directional and cannot be made exact:
 * the compiler timeout is set to be reached long after any budget a row could spend. It cannot be
 * proven — a step's cost depends on what the step does — so it is set with room rather than derived.
 */
public record EvaluationPolicy(long stepLimit, int recursionDepthLimit, Duration compilerTimeout) {

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
     * helpers. It was settled by measuring instead, against the stack a worker of this compile's own
     * is given. On sixty-four megabytes of it, a plain recursion and one carrying eight extra
     * parameters both reach a counted limit of a hundred thousand before the stack; at two hundred
     * thousand the wide one runs the stack out first, at about a hundred and fifty thousand frames.
     *
     * <p>Set below that rather than at it, and set higher than the depth any model here reaches. The
     * two ways this can be wrong are not equally bad: too low reports a legitimate deep walk as a
     * recursion that does not terminate, which is a wrong answer about the model, while too high
     * reports that the stack ran out first — which says the settings are wrong for this model and
     * what to do about it.
     *
     * <p>How much stack the execution actually gives a worker is that execution's own, and stating
     * it is how it makes room for this count to be reached first.
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
    public static final Duration DEFAULT_COMPILER_TIMEOUT = Duration.ofSeconds(60);

    /** What a compile that says nothing is held to. */
    public static final EvaluationPolicy DEFAULT = new EvaluationPolicy(DEFAULT_STEP_LIMIT,
            DEFAULT_RECURSION_DEPTH_LIMIT, DEFAULT_COMPILER_TIMEOUT);

    public EvaluationPolicy {
        if (stepLimit <= 0) {
            throw new IllegalArgumentException("a step limit has to be positive: " + stepLimit);
        }
        if (recursionDepthLimit <= 0) {
            throw new IllegalArgumentException(
                    "a recursion depth limit has to be positive: " + recursionDepthLimit);
        }
        if (compilerTimeout == null || compilerTimeout.isNegative() || compilerTimeout.isZero()) {
            throw new IllegalArgumentException(
                    "a compiler timeout has to be positive: " + compilerTimeout);
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
                Duration.ofMillis(positiveLong("souther.example.compiler.timeout.ms",
                        DEFAULT_COMPILER_TIMEOUT.toMillis())));
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
        return new EvaluationPolicy(stepLimit, DEFAULT_RECURSION_DEPTH_LIMIT, DEFAULT_COMPILER_TIMEOUT);
    }

    public EvaluationPolicy withStepLimit(long steps) {
        return new EvaluationPolicy(steps, recursionDepthLimit, compilerTimeout);
    }

    public EvaluationPolicy withRecursionDepthLimit(int depth) {
        return new EvaluationPolicy(stepLimit, depth, compilerTimeout);
    }

    public EvaluationPolicy withCompilerTimeout(Duration timeout) {
        return new EvaluationPolicy(stepLimit, recursionDepthLimit, timeout);
    }
}
