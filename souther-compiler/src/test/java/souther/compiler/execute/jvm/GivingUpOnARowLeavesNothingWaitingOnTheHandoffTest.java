package souther.compiler.execute.jvm;

import org.junit.jupiter.api.Test;

import java.time.Duration;
import java.util.concurrent.CancellationException;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.atomic.AtomicReference;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * A row that is given up on leaves no worker held by its hand-off.
 *
 * <p>Giving up is a thread that has stopped servicing hand-offs, so every way a worker could still
 * be waiting on one has to end. Two of them: a worker already inside a hand-off when the row was
 * given up on, and a worker that reaches the crossing afterwards. Both are the hand-off's, and both
 * are ended by it being terminal — nothing goes back from having been given up on to being asked.
 *
 * <p>What this does not hold is that the worker itself ends. A computation of the row's own that
 * reaches no interrupt point runs until it reaches one, which is why a worker is a daemon.
 *
 * <p>Driven with a thread servicing it, because a row that nothing is servicing is not a row: what
 * it spends is the compile's time and the servicing thread is what counts it, so a hand-off holds
 * its row until that thread arrives.
 */
class GivingUpOnARowLeavesNothingWaitingOnTheHandoffTest {

    /** A worker holding a question when the row is given up on is told, rather than left waiting. */
    @Test
    void aWorkerInsideAHandoffIsToldAndTheRowEnds() throws Exception {
        Handoff handoff = new Handoff();
        AtomicReference<Throwable> came = new AtomicReference<>();
        CountDownLatch crossed = new CountDownLatch(1);
        CountDownLatch release = new CountDownLatch(1);

        // The thread that asked for the row. Its application is held, so the row is inside the
        // hand-off waiting for an answer that has not been worked out yet.
        Thread asked = new Thread(() -> {
            try {
                handoff.serviceUntilDone(Duration.ofSeconds(30).toNanos());
            } catch (InterruptedException _) {
                Thread.currentThread().interrupt();
            }
        });
        asked.setDaemon(true);
        asked.start();

        Thread worker = new Thread(() -> {
            try {
                handoff.installedFor(() -> handoff.handOver(() -> {
                    crossed.countDown();
                    held(release);
                    return "the caller's world, still working";
                }));
            } catch (Throwable t) {
                came.set(t);
            }
        });
        worker.setDaemon(true);
        worker.start();

        crossed.await();
        waitingOnTheHandoff(worker);
        handoff.abandon();

        worker.join(10_000);
        assertFalse(worker.isAlive(), "the row ended rather than waiting for an answer");
        assertInstanceOf(CancellationException.class, came.get());
        release.countDown();
    }

    /** And a worker reaching the crossing afterwards is refused rather than made to wait. */
    @Test
    void anApplicationHandedOverAfterwardsIsRefused() {
        Handoff handoff = new Handoff();
        handoff.abandon();

        assertThrows(CancellationException.class, () -> handoff.handOver(() -> "never applied"));
    }

    /**
     * And a row that had not begun does not begin.
     *
     * <p>The other end of the same terminal phase. A row waits for the thread that counts what it
     * spends, and where that thread gave up before it arrived there is nothing to wait for — so the
     * row is told, rather than held for a wait nobody is counting.
     */
    @Test
    void aRowThatHadNotBegunIsToldRatherThanHeld() {
        Handoff handoff = new Handoff();
        handoff.abandon();

        assertThrows(CancellationException.class,
                () -> handoff.installedFor(() -> "never ran"));
        assertThrows(CancellationException.class, () -> handoff.handOver(() -> "never applied"));
    }

    /** Until {@code release} is let go of. What an application may end with is what applying an
     *  implementation may end with, and being interrupted is not among them. */
    private static void held(CountDownLatch release) {
        try {
            release.await();
        } catch (InterruptedException _) {
            Thread.currentThread().interrupt();
        }
    }

    /** Until {@code worker} is inside the hand-off, which is the only thing it waits on. */
    private static void waitingOnTheHandoff(Thread worker) {
        long until = System.nanoTime() + 10_000_000_000L;
        while (worker.getState() != Thread.State.WAITING) {
            if (System.nanoTime() > until) {
                fail("the worker never reached the hand-off: " + worker.getState());
            }
            Thread.onSpinWait();
        }
    }
}
