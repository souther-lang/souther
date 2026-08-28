package souther.compiler.examples;

import souther.compiler.diag.SourcePos;
import souther.compiler.execute.EvaluationPolicy;
import souther.compiler.observe.RowIdentity;

import java.util.concurrent.Callable;

/**
 * How long a piece of work gets, and what the caller is handed when it does not finish.
 *
 * <p>Two places give work a limit: a written statement being read ({@link ExampleStatements}) and a
 * row being evaluated ({@link ExampleVerifier}). Both do it the same way — a worker of its own and a
 * wall clock — and both did it inline, which left every test about what the compiler <em>says</em>
 * about work that overran racing a clock to say it. On a loaded host the race is lost in the
 * direction that matters: work that does finish is reported as work that did not.
 *
 * <p>So the limit is a seam. What a build uses is {@link #ofMillis}, which is what both sites did
 * before. What a test uses is a deadline that decides by which work it is, so "this row does not
 * come back" is stated rather than raced for.
 */
public interface Deadline {

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
    long DEFAULT_WORKER_STACK_BYTES = 64L * 1024 * 1024;

    /** The stack this JVM's settings ask a worker to be given, read the way {@link
     *  EvaluationPolicy#fromSettings} reads the terms. */
    static long workerStackFromSettings() {
        return EvaluationPolicy.positiveLong("souther.example.worker.stack.bytes",
                DEFAULT_WORKER_STACK_BYTES);
    }

    /**
     * One piece of work, said as what it is rather than as a sentence about it.
     *
     * <p>A deadline a test writes decides by reading this, so what it carries has to say which piece
     * of work it is. Where the writing is says that for any of them, and a row written with a name
     * says it as well: a name is unique among the rows one behavior has, over the module's own source
     * and every file attached to it, so a test may match on either. Editing a name is renaming the
     * row, and a deadline matched on the old one no longer meets it — which is what a rename is.
     */
    sealed interface Work {

        /** The behavior this work is about. */
        String target();

        /** Where the writing this is about starts, which says which source it is in. */
        SourcePos pos();

        /** A row of an {@code example}, evaluated: its fixtures built, the behavior applied, the
         * result compared. {@code identity} is what the row names itself. */
        record Row(String target, SourcePos pos, RowIdentity identity) implements Work {}

        /** The statements a row is read from, with no behavior applied. */
        record Fixtures(String target, SourcePos pos, RowIdentity identity) implements Work {}

        /** A {@code fake} table, built. */
        record Table(String target, SourcePos pos) implements Work {}

        /** A {@code with} written on a row. */
        record With(String target, SourcePos pos) implements Work {}
    }

    /** How many milliseconds this allows. What a report about an overrun quotes. */
    long budgetMs();

    /** {@code work}, run within what this allows. */
    <T> Outcome<T> given(Work work, Callable<T> work0);

    /** What became of work that was given a deadline. */
    sealed interface Outcome<T> {

        /** It finished, and this is what it answered. */
        record Finished<T>(T value) implements Outcome<T> {}

        /**
         * It did not finish.
         *
         * <p>{@code abandon} gives up on it, and is separate from this arriving because the two are
         * ordered: work that overran may have published how far it got, and giving up interrupts it,
         * so a caller that wants to know reads first and abandons after. A caller with nothing to
         * read still has to call it — nothing else will.
         */
        record Overran<T>(Runnable abandon) implements Outcome<T> {}

        /** It ended by throwing, and this is what came out. */
        record Threw<T>(Throwable cause) implements Outcome<T> {}
    }

    /** The deadline a build runs on: a worker of its own on the default stack, and {@code budgetMs}
     *  on the clock. */
    static Deadline ofMillis(long budgetMs) {
        return ofMillis(budgetMs, 0L);
    }

    /**
     * A worker of this compile's own, and no clock: what the row hands outside runs on the thread
     * that asked.
     *
     * <p>For a run whose answers come from outside the compile. Two things have to hold at once and
     * they look like they conflict. A row is one thread's from beginning to end — what it spends is
     * counted there, and how deep it may recurse is decided by the stack that thread was made with,
     * which is why {@link #DEFAULT_WORKER_STACK_BYTES} is said outright rather than inherited
     * from whatever {@code -Xss} the surrounding JVM has. And a supplied implementation answers out
     * of the caller's world, of which a thread is part — a transaction bound to one, a security or
     * request context, an MDC, a scoped value — so it has to run where the caller called from.
     *
     * <p>Both hold once the boundary is drawn at what each side owns rather than at the row. The row
     * runs on the worker and stays there; the application crosses back through {@link Handoff}, which
     * this thread services while the worker waits. So a model's recursion limit means the same thing
     * here as in a build, and the implementation still runs in the world the caller arranged.
     *
     * <p>What is given up is the clock, and only the clock. A row's counted limits are counted in the
     * code and thrown from it, so they arrive as {@link Outcome.Threw} exactly as they do on a build's
     * worker; a wall clock guards code this compile generated, and there is none of that past the
     * crossing. An implementation that does not return does not return, which is what calling one
     * synchronously is: what bounds a database query, an HTTP call or a whole test run belongs to
     * whoever owns the world, and each of those has its own way of saying so.
     */
    static Deadline crossingBackToTheCaller(long stackBytes) {
        return new Deadline() {

            @Override
            public long budgetMs() {
                return 0L;   // nothing here is bounded by a clock
            }

            @Override
            public <T> Outcome<T> given(Work work, Callable<T> body) {
                Handoff handoff = new Handoff();
                java.util.concurrent.FutureTask<T> task =
                        new java.util.concurrent.FutureTask<>(() -> handoff.installedFor(body));
                Thread worker = new Thread(null, task, "souther-reading", stackBytes);
                worker.setDaemon(true);
                worker.start();
                try {
                    handoff.serviceUntilDone();
                    return new Outcome.Finished<>(task.get());
                } catch (java.util.concurrent.ExecutionException ee) {
                    return new Outcome.Threw<>(ee.getCause());
                } catch (InterruptedException _) {
                    task.cancel(true);
                    Thread.currentThread().interrupt();
                    return new Outcome.Threw<>(
                            new java.util.concurrent.CancellationException(
                                    "interrupted while reading " + work.target()));
                }
            }
        };
    }

    /**
     * The same, on a worker given {@code stackBytes} of stack.
     *
     * <p>Said rather than inherited, so how deep a recursion gets before the stack runs out is this
     * compile's answer and not whatever {@code -Xss} the surrounding JVM was started with. The depth a
     * recursion is actually held to is counted ({@link EvaluationPolicy#recursionDepthLimit}); this is
     * what makes room for that count to be reached first.
     *
     * <p>{@code 0} asks for the platform default, which is what the JVM does with the argument.
     */
    static Deadline ofMillis(long budgetMs, long stackBytes) {
        return new Deadline() {

            @Override
            public long budgetMs() {
                return budgetMs;
            }

            @Override
            public <T> Outcome<T> given(Work work, Callable<T> body) {
                java.util.concurrent.FutureTask<T> task = new java.util.concurrent.FutureTask<>(body);
                // A daemon, because work that overran is asked to stop and cannot be made to: a
                // fixture's helper reaches no interrupt point, so the thread may outlive the answer
                // about it and must not outlive the JVM.
                Thread worker = new Thread(null, task, "souther-reading", stackBytes);
                worker.setDaemon(true);
                worker.start();
                try {
                    return new Outcome.Finished<>(
                            task.get(budgetMs, java.util.concurrent.TimeUnit.MILLISECONDS));
                } catch (java.util.concurrent.TimeoutException _) {
                    return new Outcome.Overran<>(() -> task.cancel(true));
                } catch (java.util.concurrent.ExecutionException ee) {
                    task.cancel(true);
                    return new Outcome.Threw<>(ee.getCause());
                } catch (InterruptedException _) {
                    task.cancel(true);
                    Thread.currentThread().interrupt();
                    return new Outcome.Threw<>(
                            new java.util.concurrent.CancellationException(
                                    "interrupted while reading " + work.target()));
                }
            }
        };
    }
}
