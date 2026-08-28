package souther.compiler.examples;

import souther.compiler.execute.jvm.JvmDeadlines;
import souther.compiler.execute.jvm.JvmExampleDeadlines;

import java.time.Duration;
import java.util.concurrent.Callable;
import java.util.concurrent.CancellationException;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.FutureTask;

/**
 * A worker of this compile's own, and no clock: what a row hands outside runs on the thread that
 * asked.
 *
 * <p>For a run whose answers come from outside the compile, and for no other. The rows a Java
 * binding drives reach an implementation the compile did not write; the rows a compile decides for
 * itself do not, and they keep the wait {@link souther.compiler.execute.EvaluationPolicy} states
 * under the arrangement a build uses. What the two runs have to agree on is the program and the
 * terms, which they do; giving them one arrangement as well would hand the compile's own evaluation
 * a way of running it that was made for somewhere else.
 *
 * <p>Two things have to hold at once and they look like they conflict. A row is one thread's from beginning
 * to end: what it spends is counted there, and how deep it may recurse is decided by the stack that
 * thread was made with, which is why the stack is said outright rather than inherited from whatever
 * {@code -Xss} the surrounding JVM has. And a supplied implementation answers out of the caller's
 * world, of which a thread is part — a transaction bound to one, a security or request context, an
 * MDC, a scoped value — so it has to run where the caller called from.
 *
 * <p>Both hold once the boundary is drawn at what each side owns rather than at the row. The row
 * runs on the worker and stays there; the application crosses back through {@link Handoff}, which
 * this thread services while the worker waits. So a model's recursion limit means the same thing
 * here as in a build, and the implementation still runs in the world the caller arranged.
 *
 * <p>Here rather than beside {@link JvmDeadlines}, which is where the other arrangement is, because
 * the crossing is half of a pair: the row hands over through {@link Handoff} and
 * {@link BoundImplementation} takes it up, both of which are this package's and neither of which is
 * anything a second arrangement would want. Moving this out would make them public to say so.
 */
final class CallerCrossingDeadlines implements JvmExampleDeadlines {

    private final long workerStackBytes;

    CallerCrossingDeadlines(long workerStackBytes) {
        this.workerStackBytes = workerStackBytes;
    }

    /**
     * The arrangement a bound run is run under.
     *
     * <p>{@code outerTimeout} is what the compile said it would give a row, and this does not keep
     * it. {@link souther.compiler.execute.EvaluationPolicy} obliges an execution to elapsed time —
     * past the wait, the caller is not still waiting — and a bound run does not discharge that: what
     * is given up here is the clock, and only the clock. A row's counted limits are counted in the
     * code and thrown from it, so they arrive as {@link Deadline.Outcome.Threw} exactly as they do
     * on a build's worker; a wall clock guards code this compile generated, and there is none of
     * that past the crossing. An implementation that does not return does not return, which is what
     * calling one synchronously is: what bounds a database query, an HTTP call or a whole test run
     * belongs to whoever owns the world.
     *
     * <p>That is a debt and not a reading of the term. Bounding the wait of a row that is partly the
     * caller's own thread is its own design — the wait has to stop while the crossing is being
     * serviced and start again after — and until it is written the wait a bound run is held to is
     * whatever the caller's world holds it to. Nothing else is affected: what the compile decides
     * for itself runs under {@code JvmDeadlines}, which keeps the wait.
     */
    @Override
    public Deadline forThisCompile(Duration outerTimeout) {
        return new Deadline() {

            @Override
            public long budgetMs() {
                // What this waits, and so what it would have a report quote. Nothing does: a budget
                // is quoted by a report about work that overran, and no work under this one does.
                return 0L;
            }

            @Override
            public <T> Outcome<T> given(Work work, Callable<T> body) {
                Handoff handoff = new Handoff();
                FutureTask<T> task = new FutureTask<>(() -> handoff.installedFor(body));
                Thread worker = new Thread(null, task, "souther-reading", workerStackBytes);
                worker.setDaemon(true);
                worker.start();
                try {
                    handoff.serviceUntilDone();
                    return new Outcome.Finished<>(task.get());
                } catch (ExecutionException ee) {
                    return new Outcome.Threw<>(ee.getCause());
                } catch (InterruptedException _) {
                    task.cancel(true);
                    Thread.currentThread().interrupt();
                    return new Outcome.Threw<>(new CancellationException(
                            "interrupted while reading " + work.target()));
                }
            }
        };
    }
}
