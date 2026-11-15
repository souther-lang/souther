package souther.test;

import java.time.Duration;
import java.util.Arrays;

import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Threads a test starts, so that none outlives it and none is let go of unasked.
 *
 * <p>A worker is a daemon: one a test did not wait for must not keep the JVM alive, and a worker
 * that never ends is the test's finding and not the build's. What a test claims by starting one is
 * either that it does not matter whether it ended, which {@link #started} serves, or that it ended,
 * which {@link #ended} asks and answers with where the worker is standing when it did not.
 */
public final class Workers {

    private Workers() {
    }

    /** Runs {@code body} on a daemon thread called {@code name}. */
    public static Thread started(String name, Runnable body) {
        Thread worker = new Thread(body, name);
        worker.setDaemon(true);
        worker.start();
        return worker;
    }

    /**
     * Waits up to {@code bound} for {@code worker} to end and fails if it has not, saying {@code
     * claim} and the stack the worker is in. The bound is for a worker that is not going to end; a
     * slow one ends the wait when it does.
     */
    public static void ended(Thread worker, Duration bound, String claim) {
        try {
            worker.join(bound);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            throw new AssertionError("interrupted waiting for " + worker.getName(), e);
        }
        assertFalse(worker.isAlive(), () -> claim + ": " + worker.getName() + " is still running, in\n"
                + String.join("\n", Arrays.stream(worker.getStackTrace())
                        .map(frame -> "    at " + frame).toList()));
    }
}
