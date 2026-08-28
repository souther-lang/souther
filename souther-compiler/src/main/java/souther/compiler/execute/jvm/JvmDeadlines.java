package souther.compiler.execute.jvm;

import souther.compiler.examples.Deadline;
import souther.compiler.execute.EvaluationPolicy;

import java.util.concurrent.Callable;
import java.util.concurrent.CancellationException;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.FutureTask;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

/**
 * The deadlines this machine keeps, and the words only this machine has for them.
 *
 * <p>{@link Deadline} says what a deadline is: work goes in, an outcome comes out. Saying it is not
 * running it, and what runs it here is a thread of this compile's own and a wall clock. A thread and
 * a number of bytes of stack are this machine's vocabulary and nothing else's, so they are said here
 * rather than on the protocol every reader of a row holds.
 */
public final class JvmDeadlines {

    /**
     * The stack a worker is given.
     *
     * <p>Large, and said here rather than inherited, so that how deep a recursion gets before the
     * stack runs out is not something the surrounding JVM decides. What is meant to stop a recursion
     * is {@link EvaluationPolicy#recursionDepthLimit}, which is counted and is the same on every
     * machine; this is what makes room for that count to be reached first, and how much room it makes
     * is what that limit was measured against.
     *
     * <p>A number of bytes of a thread's stack is this arrangement's and no other's. An execution
     * that runs a row some other way bounds its recursion its own way and has nothing to do with
     * this, which is why it is not among the terms a run is held to.
     */
    private static final long DEFAULT_WORKER_STACK_BYTES = 64L * 1024 * 1024;

    /** The stack this JVM's settings ask a worker to be given, on the terms
     *  {@link EvaluationPolicy#fromSettings} states: a setting that is missing, unreadable or not
     *  positive leaves the default in place. */
    public static long workerStackFromSettings() {
        String written = System.getProperty("souther.example.worker.stack.bytes");
        if (written == null) {
            return DEFAULT_WORKER_STACK_BYTES;
        }
        try {
            long asked = Long.parseLong(written.trim());
            return asked > 0 ? asked : DEFAULT_WORKER_STACK_BYTES;
        } catch (NumberFormatException _) {
            return DEFAULT_WORKER_STACK_BYTES;
        }
    }

    /** A worker on the platform's own stack, and {@code budgetMs} on the clock. */
    public static Deadline ofMillis(long budgetMs) {
        return ofMillis(budgetMs, 0L);
    }

    /**
     * A worker given {@code stackBytes} of stack, and {@code budgetMs} on the clock.
     *
     * <p>The stack is said rather than inherited, so how deep a recursion gets before it runs out is
     * this compile's answer and not whatever {@code -Xss} the surrounding JVM was started with. The
     * depth a recursion is actually held to is counted
     * ({@link EvaluationPolicy#recursionDepthLimit}); this is what makes room for that count to be
     * reached first.
     *
     * <p>{@code 0} asks for the platform default, which is what the JVM does with the argument.
     */
    public static Deadline ofMillis(long budgetMs, long stackBytes) {
        return new Deadline() {

            @Override
            public long budgetMs() {
                return budgetMs;
            }

            @Override
            public <T> Deadline.Outcome<T> given(Deadline.Work work, Callable<T> body) {
                FutureTask<T> task = new FutureTask<>(body);
                // A daemon, because work that overran is asked to stop and cannot be made to: a
                // fixture's helper reaches no interrupt point, so the thread may outlive the answer
                // about it and must not outlive the JVM.
                Thread worker = new Thread(null, task, "souther-reading", stackBytes);
                worker.setDaemon(true);
                worker.start();
                try {
                    return new Deadline.Outcome.Finished<>(
                            task.get(budgetMs, TimeUnit.MILLISECONDS));
                } catch (TimeoutException _) {
                    return new Deadline.Outcome.Overran<>(() -> task.cancel(true));
                } catch (ExecutionException ee) {
                    task.cancel(true);
                    return new Deadline.Outcome.Threw<>(ee.getCause());
                } catch (InterruptedException _) {
                    task.cancel(true);
                    Thread.currentThread().interrupt();
                    return new Deadline.Outcome.Threw<>(
                            new CancellationException("interrupted while reading " + work.target()));
                }
            }
        };
    }

    /** The arrangement a build runs on: a worker of this compile's own, made with the stack this
     *  JVM's settings ask for, and the compile's own wait on the clock. */
    public static JvmExampleDeadlines onWorkers() {
        long stackBytes = workerStackFromSettings();
        return outerTimeout -> ofMillis(outerTimeout.toMillis(), stackBytes);
    }

    private JvmDeadlines() {
    }
}
