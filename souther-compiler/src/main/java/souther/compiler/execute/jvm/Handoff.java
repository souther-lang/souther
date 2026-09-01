package souther.compiler.execute.jvm;

import souther.compiler.examples.CallerApplication;

import java.util.concurrent.Callable;
import java.util.concurrent.CancellationException;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;

/**
 * Where a row's evaluation hands work back to the thread that asked for it.
 *
 * <p>A row is one thread's from beginning to end and has to be: what it spends is counted on that
 * thread ({@code EvaluationContext}), what it went through is collected there ({@code Probe}), and
 * how deep it may recurse is decided by the stack that thread was made with — a number of bytes the
 * arrangement running the row says outright ({@link JvmDeadlines}) rather than inherits.
 * Splitting a row across two threads would take the counting apart, and running it on whatever
 * thread called would put a model's recursion limit at the mercy of the surrounding {@code -Xss}.
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
 * between a row and what applies it. What is threaded is {@link CallerApplication}, which says that
 * an application is applied in the caller's world and says nothing of a thread; this is how one
 * machine answers it.
 *
 * <p>One {@link Phase} at a time and one lock over it, so that what may hold at once is decided by
 * which phase this is in rather than by which combinations of separate fields were meant to be
 * possible. Every transition is taken under the lock, which is what makes {@link Phase.Abandoned}
 * terminal in the way that matters: a row given up on cannot be asked again between the giving up
 * and the asking, so nothing is left waiting on an answer nobody is coming to give.
 */
final class Handoff {

    private static final ThreadLocal<Handoff> ON_THIS_THREAD = new ThreadLocal<>();

    /**
     * Where a hand-off is between the two threads it is shared by.
     *
     * <p>Exclusive, and holding what that phase has rather than sitting beside it. What is being
     * applied belongs to a hand-off that was asked and to no other phase, and what came of it
     * belongs to one that was answered, so neither is a field that some other phase has to be
     * remembered not to read.
     */
    private sealed interface Phase {

        /** The row is on its worker and nothing is handed over. */
        record Running() implements Phase {}

        /** The row is waiting for {@code application} to be applied where the caller called from. */
        record Asked(CallerApplication.Application application) implements Phase {}

        /** The application was applied, and this is what came of it. */
        record Answered(Object value, Throwable threw) implements Phase {}

        /** The row left its worker, whichever way it left. */
        record Done() implements Phase {}

        /** The row was given up on. Nothing leaves this. */
        record Abandoned() implements Phase {}
    }

    private final ReentrantLock lock = new ReentrantLock();

    /** Told to whoever is waiting for the other side to move. */
    private final Condition moved = lock.newCondition();

    private Phase phase = new Phase.Running();

    /**
     * The caller's world, reached from whichever worker is running the row.
     *
     * <p>One value for every row, because what it answers is a question about the thread it is
     * asked on. A row applying an implementation is on a worker this arrangement made, and that
     * worker was given the hand-off of the run it belongs to.
     */
    static CallerApplication onTheThreadThatAsked() {
        return application -> {
            Handoff back = ON_THIS_THREAD.get();
            if (back == null) {
                // Not a row of a bound run, or a worker made by something that does not service
                // hand-offs. Applying it here would run the caller's code on a thread the caller
                // never called from, which is the one thing a crossing is for.
                throw new IllegalStateException("an implementation supplied from outside was"
                        + " applied on a thread with no way back to the caller");
            }
            return back.handOver(application);
        };
    }

    /** Whether the thread asking is a row's worker, which is where a hand-off is installed. */
    static boolean onARowsWorker() {
        return ON_THIS_THREAD.get() != null;
    }

    /** Makes this the hand-off of the thread that calls it, for as long as {@code body} runs. */
    <T> T installedFor(Callable<T> body) throws Exception {
        ON_THIS_THREAD.set(this);
        try {
            return body.call();
        } finally {
            ON_THIS_THREAD.remove();
            left();
        }
    }

    /**
     * {@code application}, applied on the thread waiting for it, and what it answered.
     *
     * <p>What it threw comes back as it was thrown, which is what {@link CallerApplication} says an
     * application ends with. Whose failure it is and what it means for the row are read where the
     * row is, and a hand-off that wrapped it would be a second thing to unwrap — and would have the
     * throw a supplied implementation ends with read as one failure here and another where a row
     * applies where it stands.
     *
     * @throws CancellationException where the row was given up on, either before this was asked or
     *                               while it was waiting for the answer
     */
    Object handOver(CallerApplication.Application application) throws ReflectiveOperationException {
        lock.lock();
        try {
            switch (phase) {
                case Phase.Running _ -> phase = new Phase.Asked(application);
                case Phase.Abandoned _ -> throw givenUpOn();
                // A row hands one application over at a time, and a row that has left is not
                // handing anything over at all.
                default -> throw new IllegalStateException(
                        "an application was handed over by a row that is " + phase);
            }
            moved.signalAll();
            while (phase instanceof Phase.Asked) {
                moved.await();
            }
            if (!(phase instanceof Phase.Answered(Object value, Throwable threw))) {
                throw givenUpOn();
            }
            phase = new Phase.Running();
            moved.signalAll();
            switch (threw) {
                case null -> {
                    return value;
                }
                case RuntimeException re -> throw re;
                case Error e -> throw e;
                case ReflectiveOperationException roe -> throw roe;
                // An application ends with one of the three above, so this is the hand-off being
                // given something that is not an application to apply.
                default -> throw new IllegalStateException(threw);
            }
        } catch (InterruptedException _) {
            Thread.currentThread().interrupt();
            throw new CancellationException(
                    "interrupted while handing an application to the thread that asked for it");
        } finally {
            lock.unlock();
        }
    }

    /** How servicing a row's hand-offs ended. */
    enum Serviced {

        /** The row left its worker, and what it left is the task's to say. */
        ROW_LEFT,

        /** The row spent the wait it was given, without leaving. */
        WAIT_SPENT
    }

    /**
     * Applies whatever the row hands over, here, until the row leaves its worker or spends
     * {@code waitNanos} of this compile's own time.
     *
     * <p>Called by the thread that asked for the row, which is why what runs here runs in the world
     * that thread is in. The application is applied with the lock let go of: it is the caller's own
     * code, it may take as long as the caller's world takes, and holding a lock the row needs
     * across it would make the row wait for the caller's database.
     *
     * <p>That is also what makes the wait measurable here and nowhere else. This thread is idle
     * exactly while the other side is the one working — a row on its worker, or a worker taking up
     * the answer it was given — and it is awake and working exactly while the application is. So the
     * wait is what {@link Condition#awaitNanos} spends and nothing else: what the caller's own code
     * takes is never inside one, and is not left out by being subtracted but by never being counted.
     *
     * <p>A hand-off that arrived is taken up whatever the clock says. The wait is spent only where
     * nothing was handed over, so an application that reached the crossing before the wait ran out
     * is applied rather than being given up on for the scheduler's sake.
     */
    Serviced serviceUntilDone(long waitNanos) throws InterruptedException {
        long remaining = waitNanos;
        while (true) {
            CallerApplication.Application application;
            lock.lock();
            try {
                while (phase instanceof Phase.Running || phase instanceof Phase.Answered) {
                    if (remaining <= 0) {
                        return Serviced.WAIT_SPENT;
                    }
                    remaining = moved.awaitNanos(remaining);
                }
                if (!(phase instanceof Phase.Asked(CallerApplication.Application asked))) {
                    return Serviced.ROW_LEFT;   // the row left, or was given up on
                }
                application = asked;
            } finally {
                lock.unlock();
            }

            Object value = null;
            Throwable threw = null;
            try {
                value = application.call();
            } catch (Throwable t) {
                threw = t;
            }

            lock.lock();
            try {
                // Only where the row is still waiting for it. Given up on while its application was
                // being applied, the row is gone and an answer put here would be read by nobody.
                if (phase instanceof Phase.Asked) {
                    phase = new Phase.Answered(value, threw);
                    moved.signalAll();
                }
            } finally {
                lock.unlock();
            }
        }
    }

    /**
     * Gives up on the row, so that nothing of it is left waiting on this.
     *
     * <p>Terminal. A row given up on is not asked again and is not answered, so a worker inside a
     * hand-off is told here rather than left holding a question, and one that reaches the crossing
     * afterwards is refused rather than made to wait for a thread that has stopped servicing.
     *
     * <p>What this does not end is a computation of the row's own that reaches no interrupt point.
     * That is the worker's to notice and this has nothing to say about it; what is closed here is
     * the hand-off, which is the one thing that could hold a worker that would otherwise finish.
     */
    void abandon() {
        lock.lock();
        try {
            phase = new Phase.Abandoned();
            moved.signalAll();
        } finally {
            lock.unlock();
        }
    }

    /** Where the row left its worker: done, unless it had already been given up on. */
    private void left() {
        lock.lock();
        try {
            if (!(phase instanceof Phase.Abandoned)) {
                phase = new Phase.Done();
            }
            moved.signalAll();
        } finally {
            lock.unlock();
        }
    }

    private static CancellationException givenUpOn() {
        return new CancellationException(
                "the row this application belongs to was given up on");
    }
}
