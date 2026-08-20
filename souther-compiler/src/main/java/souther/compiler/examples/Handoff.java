package souther.compiler.examples;

import java.util.concurrent.Callable;
import java.util.concurrent.SynchronousQueue;

/**
 * Where a row's evaluation hands work back to the thread that asked for it.
 *
 * <p>A row is one thread's from beginning to end and has to be: what it spends is counted on that
 * thread ({@code EvaluationContext}), what it went through is collected there ({@code Probe}), and
 * how deep it may recurse is decided by the stack that thread was made with
 * ({@link EvaluationPolicy#workerStackBytes}). Splitting a row across two threads would take the
 * counting apart, and running it on whatever thread called would put a model's recursion limit at
 * the mercy of the surrounding {@code -Xss}.
 *
 * <p>An implementation supplied from outside is the one part of a row that is not this compile's
 * computation. What it answers out of is the caller's world, and a thread is part of a world — a
 * transaction bound to one, a security or request context, an MDC, a scoped value — so it has to run
 * where the caller called from, and nothing about a synchronous {@code evaluate(row)} says
 * otherwise.
 *
 * <p>The two are not in conflict once the boundary is drawn at what each side owns rather than at
 * the row. The row runs on this compile's own worker and stays there; when it reaches the crossing
 * it hands the application over here, the caller's thread runs it, and the answer goes back. One
 * hand-off per application, and the worker is alive on either side of it, so nothing the row was
 * counting is interrupted.
 *
 * <p>Installed on the worker and read from it, so nothing has to be threaded through the seam
 * between a row and what applies it. A run with no hand-off — every compile-time run — finds none
 * and applies where it stands.
 */
final class Handoff {

    /** Posted when the row is done, so the thread servicing hand-offs stops waiting for another. */
    private static final Object NO_MORE = new Object();

    private static final ThreadLocal<Handoff> ON_THIS_THREAD = new ThreadLocal<>();

    private final SynchronousQueue<Object> asked = new SynchronousQueue<>();
    private final SynchronousQueue<Answered> answered = new SynchronousQueue<>();

    /** What came of running one hand-off: what it answered, or what it threw. */
    private record Answered(Object value, Throwable threw) {}

    /** The hand-off this thread was given, or null where it is not a row's worker. */
    static Handoff onThisThread() {
        return ON_THIS_THREAD.get();
    }

    /** Makes this the hand-off of the thread that calls it, for as long as {@code body} runs. */
    <T> T installedFor(Callable<T> body) throws Exception {
        ON_THIS_THREAD.set(this);
        try {
            return body.call();
        } finally {
            ON_THIS_THREAD.remove();
            // Whichever way the row left, the thread waiting on hand-offs is told there are no more.
            // Left unsaid it would wait for one that is never coming.
            putUninterruptibly(asked, NO_MORE);
        }
    }

    /**
     * {@code work}, run on the thread waiting for it, and what it answered.
     *
     * <p>What it threw comes back as it was thrown. Whose failure it is and what it means for the row
     * are read where the row is, and a hand-off that wrapped it would be a second thing to unwrap.
     */
    Object handOver(Callable<Object> work) {
        try {
            asked.put(work);
            Answered came = answered.take();
            if (came.threw() != null) {
                throw came.threw() instanceof RuntimeException re ? re
                        : new IllegalStateException(came.threw());
            }
            return came.value();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            throw new java.util.concurrent.CancellationException(
                    "interrupted while handing an application to the thread that asked for it");
        }
    }

    /**
     * Runs whatever the row hands over, here, until the row is done.
     *
     * <p>Called by the thread that asked for the row, which is why what runs here runs in the world
     * that thread is in.
     */
    void serviceUntilDone() throws InterruptedException {
        while (true) {
            Object next = asked.take();
            if (next == NO_MORE) {
                return;
            }
            @SuppressWarnings("unchecked")
            Callable<Object> work = (Callable<Object>) next;
            Answered came;
            try {
                came = new Answered(work.call(), null);
            } catch (Throwable t) {
                came = new Answered(null, t);
            }
            answered.put(came);
        }
    }

    private static void putUninterruptibly(SynchronousQueue<Object> into, Object what) {
        boolean interrupted = false;
        while (true) {
            try {
                into.put(what);
                break;
            } catch (InterruptedException _) {
                interrupted = true;
            }
        }
        if (interrupted) {
            Thread.currentThread().interrupt();
        }
    }
}
