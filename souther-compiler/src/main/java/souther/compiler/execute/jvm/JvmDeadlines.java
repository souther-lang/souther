package souther.compiler.execute.jvm;

import souther.compiler.examples.Deadline;
import souther.compiler.execute.EvaluationPolicy;

import java.time.Duration;
import java.util.concurrent.Callable;
import java.util.concurrent.CancellationException;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.FutureTask;

/**
 * The deadlines this machine keeps, and the words only this machine has for them.
 *
 * <p>{@link Deadline} says what a deadline is: work goes in, an outcome comes out. Saying it is not
 * running it, and what runs it here is a thread of this compile's own, a hand-off, and a clock. A
 * thread and a number of bytes of stack are this machine's vocabulary and nothing else's, so they
 * are said here rather than on the protocol every reader of a row holds.
 *
 * <p>One arrangement, and a build is not a second one. A row runs on a worker of this compile's own
 * and stays there — what it spends is counted on that thread and how deep it may recurse is decided
 * by the stack that thread was made with — and what it hands outside runs on the thread that asked,
 * because an implementation supplied from outside answers out of the caller's world and a thread is
 * part of a world. A run that hands nothing over, which is every run a compile makes for itself, is
 * that same arrangement with an empty {@link Handoff}: there is no second machine to write, and a
 * second one is where two answers to what the wait counts would come from.
 *
 * <p>What the wait counts is this compile's own time. A row is given up on for having stopped
 * answering, and what the caller's own code takes is not this compiler failing to answer — a clock
 * over both would report the caller's database as a compile that would not finish. The crossing is
 * the one place a row leaves the worker, so it is the one place able to say which is which, and
 * {@link Handoff#serviceUntilDone} does: the wait is what the servicing thread spends waiting for a
 * hand-off, and an application is not left out of it by being subtracted but by never being inside
 * one.
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

    /** A worker on the platform's own stack, and {@code timeout} of this compile's own time on the
     *  clock. */
    public static Deadline of(Duration timeout) {
        return of(timeout, 0L);
    }

    /**
     * A worker given {@code stackBytes} of stack, and {@code timeout} of this compile's own time on
     * the clock.
     *
     * <p>The stack is said rather than inherited, so how deep a recursion gets before it runs out is
     * this compile's answer and not whatever {@code -Xss} the surrounding JVM was started with. The
     * depth a recursion is actually held to is counted
     * ({@link EvaluationPolicy#recursionDepthLimit}); this is what makes room for that count to be
     * reached first.
     *
     * <p>{@code 0} asks for the platform default, which is what the JVM does with the argument.
     *
     * <p>A length and not a number of milliseconds, here as on {@link Deadline#timeout}. A face
     * taking milliseconds would round before anything counted, and a wait shorter than one — which
     * the policy admits, taking any positive length — would arrive as no wait at all.
     */
    public static Deadline of(Duration timeout, long stackBytes) {
        long waitNanos = nanosOf(timeout);
        return new Deadline() {

            @Override
            public Duration timeout() {
                return timeout;
            }

            @Override
            public <T> Deadline.Outcome<T> given(Deadline.Work work, Callable<T> body) {
                if (Handoff.onARowsWorker()) {
                    // A row's worker is where the hand-off of the run it belongs to is installed,
                    // and a second run started from there would service its hand-offs on this
                    // worker rather than on the thread that asked — so the caller's code would run
                    // somewhere the caller never called from, and the time it took would be spent
                    // out of the wait the outer row is being held to.
                    //
                    // Asked here and not where the hand-off is installed, which is where the thread
                    // this reads is that hand-off's own. Refused there, the refusal would be on a
                    // worker that already exists and would leave that run with a phase nothing
                    // moves, so the thread that asked would wait out the whole wait for a run that
                    // was never going to happen.
                    throw new IllegalStateException("a row's worker cannot start a second run:"
                            + " what a run within a run is held to, and where its applications go,"
                            + " is not decided");
                }
                Handoff handoff = new Handoff();
                FutureTask<T> task = new FutureTask<>(() -> handoff.installedFor(body));
                // A daemon, because work that overran is asked to stop and cannot be made to: a
                // fixture's helper reaches no interrupt point, so the thread may outlive the answer
                // about it and must not outlive the JVM.
                Thread worker = new Thread(null, task, "souther-reading", stackBytes);
                worker.setDaemon(true);
                worker.start();
                try {
                    if (handoff.serviceUntilDone(waitNanos) == Handoff.Serviced.WAIT_SPENT) {
                        // Given up on when the caller says so and not here: what the worker
                        // published is still there to be read, and reading it comes first.
                        return new Deadline.Outcome.Overran<>(() -> {
                            handoff.abandon();
                            task.cancel(true);
                        });
                    }
                    return new Deadline.Outcome.Finished<>(task.get());
                } catch (ExecutionException ee) {
                    task.cancel(true);
                    return new Deadline.Outcome.Threw<>(ee.getCause());
                } catch (InterruptedException _) {
                    handoff.abandon();
                    task.cancel(true);
                    Thread.currentThread().interrupt();
                    return new Deadline.Outcome.Threw<>(
                            new CancellationException("interrupted while reading " + work.target()));
                }
            }
        };
    }

    /** The arrangement a run runs on, whoever drives it: a worker of this compile's own, made with
     *  the stack this JVM's settings ask for, and the compile's own wait on the clock. */
    public static JvmExampleDeadlines onWorkers() {
        long stackBytes = workerStackFromSettings();
        return compilerTimeout -> of(compilerTimeout, stackBytes);
    }

    /**
     * {@code timeout} as this clock counts, which is nanoseconds.
     *
     * <p>A length longer than nanoseconds can hold is one nothing reaches, so it is counted as the
     * longest this can count rather than refused: what the term says is how long the compiler may go
     * on without answering, and a term nothing will reach is not a term stated wrongly.
     */
    private static long nanosOf(Duration timeout) {
        try {
            return timeout.toNanos();
        } catch (ArithmeticException _) {
            return Long.MAX_VALUE;
        }
    }

    private JvmDeadlines() {
    }
}
