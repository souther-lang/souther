package souther.compiler.execute.jvm;

import org.junit.jupiter.api.Test;

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
 */
class GivingUpOnARowLeavesNothingWaitingOnTheHandoffTest {

    /** A worker holding a question when the row is given up on is told, rather than left waiting. */
    @Test
    void aWorkerInsideAHandoffIsToldAndTheRowEnds() throws Exception {
        Handoff handoff = new Handoff();
        AtomicReference<Throwable> came = new AtomicReference<>();
        CountDownLatch reached = new CountDownLatch(1);

        Thread worker = new Thread(() -> {
            try {
                handoff.installedFor(() -> {
                    reached.countDown();
                    return handoff.handOver(() -> "nothing services this");
                });
            } catch (Throwable t) {
                came.set(t);
            }
        });
        worker.setDaemon(true);
        worker.start();

        reached.await();
        waitingOnTheHandoff(worker);
        handoff.abandon();

        worker.join(10_000);
        assertFalse(worker.isAlive(), "the row ended rather than waiting for an answer");
        assertInstanceOf(CancellationException.class, came.get());
    }

    /** And a worker reaching the crossing afterwards is refused rather than made to wait. */
    @Test
    void anApplicationHandedOverAfterwardsIsRefused() {
        Handoff handoff = new Handoff();
        handoff.abandon();

        assertThrows(CancellationException.class, () -> handoff.handOver(() -> "never applied"));
    }

    /** Having been given up on is not undone by the row then leaving its worker. */
    @Test
    void aRowLeavingAfterwardsDoesNotUndoIt() throws Exception {
        Handoff handoff = new Handoff();
        handoff.abandon();
        handoff.installedFor(() -> "the row left of its own accord");

        assertThrows(CancellationException.class, () -> handoff.handOver(() -> "never applied"));
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
