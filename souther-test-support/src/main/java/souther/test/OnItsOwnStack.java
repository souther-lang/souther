package souther.test;

import java.time.Duration;
import java.util.concurrent.atomic.AtomicReference;
import java.util.function.Supplier;

/**
 * Work run on a thread with a stack of a given size, for a test about how deep something goes.
 *
 * <p>Such a test runs work it means to be large — a source nested past a bound, a chain of
 * declarations long enough to run out of a small stack — so the work coming back at all is part of
 * what it asks. A test that waits on that thread with no end to the wait answers a compiler that
 * never comes back by never coming back either, and takes the run with it. So the wait is bounded
 * here, once, and work that has not come back is a failure that says so.
 *
 * <p>The thread is a daemon: work still running past the wait is left behind and does not hold the
 * test's JVM open after the run is over.
 *
 * <p>The one place a test starts a thread with a stack of its own. {@code
 * ATestRunsWorkOnAStackOfItsOwnOnlyThroughOneDoorTest} is what asks for it.
 */
public final class OnItsOwnStack {

    /** Longer than any of these tests takes on a loaded machine, and short enough that one that
     *  never comes back is reported the same run. */
    public static final Duration WAIT = Duration.ofMinutes(2);

    private OnItsOwnStack() {}

    /**
     * Runs {@code work} on a thread with {@code stackBytes} of stack, and answers what it threw, or
     * null where it returned.
     *
     * @param what what the work is, for the failure that says it did not come back
     * @throws AssertionError where the work has not come back within {@link #WAIT}
     */
    public static Throwable run(String what, long stackBytes, Runnable work) {
        AtomicReference<Throwable> thrown = new AtomicReference<>();
        Thread running = new Thread(null, () -> {
            try {
                work.run();
            } catch (Throwable e) {
                thrown.set(e);
            }
        }, what, stackBytes);
        running.setDaemon(true);
        running.start();
        try {
            running.join(WAIT);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            throw new AssertionError("interrupted waiting for " + what, e);
        }
        if (running.isAlive()) {
            throw new AssertionError(what + " did not come back within " + WAIT.toSeconds() + "s");
        }
        return thrown.get();
    }

    /**
     * Asks {@code asked} on a thread with {@code stackBytes} of stack, and answers what it answered.
     *
     * @param what what is asked, for the failure that says it threw or did not come back
     * @throws AssertionError where it threw, with what it threw as the cause, or where it has not
     *                        come back within {@link #WAIT}
     */
    public static <T> T ask(String what, long stackBytes, Supplier<T> asked) {
        AtomicReference<T> answered = new AtomicReference<>();
        Throwable thrown = run(what, stackBytes, () -> answered.set(asked.get()));
        if (thrown != null) {
            throw new AssertionError(what + " threw", thrown);
        }
        return answered.get();
    }
}
