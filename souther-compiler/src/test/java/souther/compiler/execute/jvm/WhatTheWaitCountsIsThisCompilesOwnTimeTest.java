package souther.compiler.execute.jvm;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourcePos;
import souther.compiler.examples.Deadline;
import souther.compiler.execute.EvaluationPolicy;
import souther.compiler.observe.RowIdentity;
import souther.compiler.observe.WaitShown;

import java.time.Duration;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
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
     * held, and an arrangement services immediately. This waits before it services, which is what a
     * host that descheduled the servicing thread does.
     */
    @Test
    void aRowSpendsNothingOfItsOwnBeforeAnythingIsCountingIt() throws Exception {
        Handoff handoff = new Handoff();
        Thread worker = new Thread(() -> {
            try {
                handoff.installedFor(() -> {
                    Thread.sleep(300);
                    return "the row's own work";
                });
            } catch (Exception _) {
                // The row was given up on, which is not what this is about.
            }
        });
        worker.setDaemon(true);
        worker.start();
        Thread.sleep(600);

        assertEquals(Handoff.Serviced.WAIT_SPENT,
                handoff.serviceUntilDone(Duration.ofMillis(100)),
                "the row's own work is the compile's time whenever it was run");
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
        Deadline deadline = JvmDeadlines.of(Duration.ofMillis(200));

        Deadline.Outcome<String> came = deadline.given(WORK, () -> {
            Thread.sleep(30_000);
            return "never answered";
        });

        assertInstanceOf(Deadline.Outcome.Overran.class, came).abandon().run();
    }

    /** An application taking many times the wait spends none of it. */
    @Test
    void whatTheApplicationTakesIsNotTheCompilesToSpend() {
        Deadline deadline = JvmDeadlines.of(Duration.ofMillis(500));

        Deadline.Outcome<Object> came = deadline.given(WORK,
                () -> Handoff.onTheThreadThatAsked().call(() -> {
                    slept(2_000);
                    return "answered";
                }));

        assertEquals("answered",
                assertInstanceOf(Deadline.Outcome.Finished.class, came).value());
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
    void whatTheCompileSpendsAroundCrossingsIsOneWait() {
        Deadline deadline = JvmDeadlines.of(Duration.ofMillis(400));

        Deadline.Outcome<Object> came = deadline.given(WORK, () -> {
            for (int each = 0; each < 5; each++) {
                Thread.sleep(120);
                Handoff.onTheThreadThatAsked().call(() -> {
                    slept(150);
                    return null;
                });
            }
            return "answered";
        });

        assertInstanceOf(Deadline.Outcome.Overran.class, came).abandon().run();
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

    /** {@code ms} spent where an application is applied, which may not throw what a sleep does. */
    private static void slept(long ms) {
        try {
            Thread.sleep(ms);
        } catch (InterruptedException _) {
            Thread.currentThread().interrupt();
        }
    }
}
