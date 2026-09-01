package souther.compiler.execute.jvm;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourcePos;
import souther.compiler.examples.Deadline;
import souther.compiler.observe.RowIdentity;

import java.time.Duration;

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
     * The wait an arrangement is handed is the wait it holds.
     *
     * <p>A length, kept as one. Handed on as a number of milliseconds it would be rounded before
     * anything counted it, and a wait shorter than a millisecond — which the policy admits, taking
     * any positive length — would arrive as no wait at all.
     */
    @Test
    void theWaitIsHeldAsItWasHandedOver() {
        Duration asked = Duration.ofNanos(1_500_000);

        assertEquals(asked, JvmDeadlines.onWorkers().forThisCompile(asked).timeout());
    }

    /** A row of the compile's own that will not come back is given up on. */
    @Test
    void aRowThatStopsAnsweringSpendsTheWait() {
        Deadline deadline = JvmDeadlines.ofMillis(200);

        Deadline.Outcome<String> came = deadline.given(WORK, () -> {
            Thread.sleep(30_000);
            return "never answered";
        });

        assertInstanceOf(Deadline.Outcome.Overran.class, came).abandon().run();
    }

    /** An application taking many times the wait spends none of it. */
    @Test
    void whatTheApplicationTakesIsNotTheCompilesToSpend() {
        Deadline deadline = JvmDeadlines.ofMillis(500);

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
        Deadline deadline = JvmDeadlines.ofMillis(400);

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
        Deadline deadline = JvmDeadlines.ofMillis(30_000);

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
