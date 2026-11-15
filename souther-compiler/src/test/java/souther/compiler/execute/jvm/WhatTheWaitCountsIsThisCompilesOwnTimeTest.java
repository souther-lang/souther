package souther.compiler.execute.jvm;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourcePos;
import souther.compiler.examples.CallerApplication;
import souther.compiler.examples.Deadline;
import souther.compiler.execute.EvaluationPolicy;
import souther.compiler.observe.RowIdentity;
import souther.compiler.observe.WaitShown;
import souther.test.Workers;

import java.time.Duration;
import java.util.List;
import java.util.concurrent.Callable;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.locks.Condition;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * The wait a run is held to is spent by this compile and by nothing else.
 *
 * <p>A row is given up on for having stopped answering, and that is a fact about the compiler. What
 * a supplied implementation takes is the caller's world taking it — a transaction, an HTTP call, a
 * test runner — and a clock over both would report the caller's database as this compiler failing to
 * answer. So the wait counts the row's own time, and the crossing is where the two are told apart.
 *
 * <p>Which makes the three below one rule read three ways: what the compile spends is counted, what
 * the application spends is not, and what the compile spends on either side of a crossing is the
 * same wait rather than a fresh one each time.
 */
class WhatTheWaitCountsIsThisCompilesOwnTimeTest {

    private static final Deadline.Work WORK =
            new Deadline.Work.WholeRow("findTodo", new SourcePos(1, 1), new RowIdentity.Unnamed(1));

    /**
     * A row spends the wait from the moment it can spend anything.
     *
     * <p>The wait is read where the hand-off is serviced, so what the row does before anything is
     * servicing it is time nothing is counting. A row may not have it: a worker started and then
     * left to itself would run for as long as it liked and be found finished, and every arrangement
     * this compiler ships starts a worker before it starts servicing.
     *
     * <p>Said here rather than through an arrangement because it is the interleaving that is being
     * held, and an arrangement services immediately. The worker is first left until it cannot go
     * further without the servicing thread, which is what a host that descheduled the servicing
     * thread does, and what it has done by then is read off a flag rather than off how long it took.
     */
    @Test
    void aRowSpendsNothingOfItsOwnBeforeAnythingIsCountingIt() throws Exception {
        Handoff handoff = new Handoff();
        AtomicBoolean began = new AtomicBoolean();
        CountDownLatch release = new CountDownLatch(1);
        Thread worker = Workers.started("the-row", () -> {
            try {
                handoff.installedFor(() -> {
                    began.set(true);
                    release.await();
                    return "the row's own work";
                });
            } catch (Exception _) {
                // The row was given up on, which is not what this is about.
            }
        });
        while (worker.getState() != Thread.State.WAITING) {
            Thread.onSpinWait();
        }

        assertFalse(began.get(), "the row did not begin before anything was counting it");
        try {
            assertEquals(Handoff.Serviced.WAIT_SPENT,
                    handoff.serviceUntilDone(Duration.ofMillis(1)),
                    "the row's own work is the compile's time, which nothing ends but the wait");
        } finally {
            release.countDown();
        }
    }

    /**
     * The wait an arrangement is handed is the wait it holds, over every wait the policy admits.
     *
     * <p>Which is any positive length, and the population is that rather than the lengths a wait is
     * usually written in. Both ends have their own way of not being held: below a millisecond a wait
     * handed on as a number of them is rounded to none, and past what a {@code long} of nanoseconds
     * holds a wait converted to one does not fit at all. A middle-sized wait is held by an
     * arrangement that does neither and by one that does both, so the middle alone says nothing.
     */
    @Test
    void everyWaitThePolicyAdmitsIsHeldAsItWasHandedOver() {
        for (Duration asked : List.of(
                Duration.ofNanos(1),
                Duration.ofNanos(1_500_000),
                Duration.ofSeconds(60),
                Duration.ofNanos(Long.MAX_VALUE).plusSeconds(1),
                Duration.ofDays(365_000))) {
            new EvaluationPolicy(1L, 1, asked);   // the policy admits it

            assertEquals(asked, JvmDeadlines.onWorkers().forThisCompile(asked).timeout(),
                    () -> "held as handed: " + asked);
        }
    }

    /**
     * A wait is spent by waiting, however a wait on a condition reports what is left of one.
     *
     * <p>{@link java.util.concurrent.locks.Condition#awaitNanos} answers an estimate of what is left
     * of what it was asked for, and one that timed out answers none or fewer than none. So the
     * arithmetic has three cases and one of them is a length going past zero, which is the case a
     * wait long enough to be waited out in pieces reaches — and the only one that cannot be reached
     * by waiting for it, the shortest wait that gets there being some centuries.
     */
    @Test
    void aWaitIsSpentWhateverTheWaitReportsIsLeftOfIt() {
        Duration hour = Duration.ofHours(1);

        assertEquals(Duration.ofHours(1).minusNanos(400),
                Handoff.leftOf(hour, 1_000, 600), "some of the wait was left");
        assertEquals(Duration.ofHours(1).minusNanos(1_000),
                Handoff.leftOf(hour, 1_000, 0), "none of it was");
        assertEquals(Duration.ofHours(1).minusNanos(1_001),
                Handoff.leftOf(hour, 1_000, -1), "and it went past the end of it");

        // The piece a wait past what a `long` of nanoseconds holds is waited out in, reported as
        // having gone past its end. Taken as one number, what it spent is what does not fit.
        Duration past = Duration.ofNanos(Long.MAX_VALUE).plusSeconds(1);
        assertEquals(Duration.ofNanos(Long.MAX_VALUE).plusSeconds(1).minusNanos(Long.MAX_VALUE).minusNanos(1),
                Handoff.leftOf(past, Long.MAX_VALUE, -1),
                "a wait waited out in pieces is spent by every one of them");
    }

    /** And every one of them is written down as the wait it was, rather than as none or not at
     *  all. */
    @Test
    void everyWaitThePolicyAdmitsIsWrittenAsWhatItWas() {
        assertEquals("0.000001", WaitShown.of(Duration.ofNanos(1)));
        assertEquals("1.5", WaitShown.of(Duration.ofNanos(1_500_000)));
        assertEquals("60000", WaitShown.of(Duration.ofSeconds(60)));
        assertEquals("9223372036854.775807",
                WaitShown.of(Duration.ofNanos(Long.MAX_VALUE)));
        // 365,000 days of milliseconds, which is more than a `long` of nanoseconds holds.
        assertEquals("31536000000000", WaitShown.of(Duration.ofDays(365_000)));
    }

    /** A row of the compile's own that will not come back is given up on. */
    @Test
    void aRowThatStopsAnsweringSpendsTheWait() {
        Deadline deadline = JvmDeadlines.of(Duration.ofMillis(1));

        Deadline.Outcome<String> came = deadline.given(WORK, () -> {
            new CountDownLatch(1).await();   // until abandoned, which interrupts it
            return "never answered";
        });

        assertInstanceOf(Deadline.Outcome.Overran.class, came).abandon().run();
    }

    /**
     * Time that passes only where the servicing thread is waiting.
     *
     * <p>What it takes for the wait to be spent is the row passing time, which a row does by working
     * and which this lets a test say outright. A wait returns when the row has moved, and what is
     * left of it is what the time passed inside it took. A row says it is about to move by
     * {@link #crossing} and {@link #row}, which is what a wait that must not return before then
     * asks for, so a wake-up that is not the row's leaves it waiting.
     */
    private static final class VirtualTime implements Handoff.Spending {

        private final AtomicLong now = new AtomicLong();
        private final AtomicInteger moves = new AtomicInteger();

        void pass(Duration length) {
            now.addAndGet(length.toNanos());
        }

        /** {@code application}, handed over at the crossing. */
        Object crossing(CallerApplication.Application application)
                throws ReflectiveOperationException {
            moves.incrementAndGet();
            return Handoff.onTheThreadThatAsked().call(application);
        }

        /** {@code body}, which says it is done by returning. */
        <T> Callable<T> row(Callable<T> body) {
            return () -> {
                try {
                    return body.call();
                } finally {
                    moves.incrementAndGet();
                }
            };
        }

        @Override
        public long awaiting(Condition moved, long nanos) throws InterruptedException {
            long began = now.get();
            int seen = moves.get();
            while (moves.get() == seen) {
                moved.await();
            }
            return nanos - (now.get() - began);
        }
    }

    /** Runs {@code row} as the row of {@code handoff}, on a worker of its own. */
    private static void startRow(Handoff handoff, Callable<Object> row) {
        Workers.started("the-row", () -> {
            try {
                handoff.installedFor(row);
            } catch (Exception _) {
                // Given up on, which is how a test ends a row that has stopped.
            }
        });
    }

    /** An application taking three times the wait spends none of it. */
    @Test
    void whatTheApplicationTakesIsNotTheCompilesToSpend() throws Exception {
        VirtualTime time = new VirtualTime();
        Handoff handoff = new Handoff(time);
        startRow(handoff, time.row(() -> time.crossing(() -> {
            time.pass(Duration.ofMillis(300));
            return "answered";
        })));

        assertEquals(Handoff.Serviced.ROW_LEFT, handoff.serviceUntilDone(Duration.ofMillis(100)));
    }

    /** The same, through the deadline an example is run under: what it takes of the caller is not
     *  what it is held to. */
    @Test
    void aDeadlineIsNotSpentByWhatTheApplicationTakes() {
        VirtualTime time = new VirtualTime();
        Deadline deadline = JvmDeadlines.of(Duration.ofMillis(100), 0L, time);

        Deadline.Outcome<Object> came = deadline.given(WORK, time.row(() -> time.crossing(() -> {
            time.pass(Duration.ofMillis(300));
            return "answered";
        })));

        assertEquals("answered", assertInstanceOf(Deadline.Outcome.Finished.class, came).value());
    }

    /**
     * And the compile's own time on either side of a crossing is one wait, through the deadline.
     * The stretches are those of {@link #whatTheCompileSpendsAroundCrossingsIsOneWait}.
     */
    @Test
    void aDeadlineIsSpentByTheCompilesOwnTimeAroundCrossingsAsOneWait() {
        VirtualTime time = new VirtualTime();
        Deadline deadline = JvmDeadlines.of(Duration.ofMillis(100), 0L, time);

        Deadline.Outcome<Object> came = deadline.given(WORK, time.row(() -> {
            for (int each = 0; each < 5; each++) {
                time.pass(Duration.ofMillis(30));
                time.crossing(() -> {
                    time.pass(Duration.ofMillis(40));
                    return null;
                });
            }
            return "answered";
        }));

        assertInstanceOf(Deadline.Outcome.Overran.class, came).abandon().run();
    }

    /**
     * And the compile's own time on either side of a crossing is one wait.
     *
     * <p>Five stretches of the row's own, none of them near the wait and their sum past it, with an
     * application longer than any of them between each pair. A wait that started again at every
     * crossing would see five short stretches and never be reached; one that counted the
     * applications would be reached in the first stretch, which is what the reading above holds
     * against.
     */
    @Test
    void whatTheCompileSpendsAroundCrossingsIsOneWait() throws Exception {
        VirtualTime time = new VirtualTime();
        Handoff handoff = new Handoff(time);
        startRow(handoff, time.row(() -> {
            for (int each = 0; each < 5; each++) {
                time.pass(Duration.ofMillis(30));
                time.crossing(() -> {
                    time.pass(Duration.ofMillis(40));
                    return null;
                });
            }
            return "answered";
        }));

        try {
            assertEquals(Handoff.Serviced.WAIT_SPENT,
                    handoff.serviceUntilDone(Duration.ofMillis(100)));
        } finally {
            handoff.abandon();
        }
    }

    /**
     * A row's worker does not start a second run.
     *
     * <p>Its hand-off is the one of the run it belongs to, so a run started from there would have
     * its applications serviced on this worker rather than on the thread that asked — the caller's
     * code somewhere the caller never called from — and the time they took would come out of the
     * wait the outer row is held to. What a run within a run is held to is not decided, so it is
     * refused where it is asked for rather than answered wrongly.
     */
    @Test
    void aRowsWorkerDoesNotStartASecondRun() {
        Deadline deadline = JvmDeadlines.of(Duration.ofSeconds(30));

        Deadline.Outcome<Object> came = deadline.given(WORK,
                () -> deadline.given(WORK, () -> "a run within a run"));

        assertInstanceOf(IllegalStateException.class,
                assertInstanceOf(Deadline.Outcome.Threw.class, came).cause());
    }
}
