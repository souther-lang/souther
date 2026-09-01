package souther.compiler.execute.jvm;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourcePos;
import souther.compiler.examples.Deadline;
import souther.compiler.examples.InvocationFailure;
import souther.compiler.observe.RowIdentity;

import java.lang.reflect.InvocationTargetException;
import java.time.Duration;
import java.util.concurrent.atomic.AtomicReference;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row runs where this compile says and what it hands outside runs where the caller called from.
 *
 * <p>The two look like one question and are two. A row is one thread's from beginning to end: what
 * it spends is counted there, what it went through is collected there, and how deep it may recurse
 * is decided by the stack that thread was made with — which is why the arrangement says how much
 * stack outright rather than inheriting whatever {@code -Xss} the surrounding JVM has. An implementation
 * supplied from outside is the one part of a row that is not this compile's computation, and what it
 * answers out of is the caller's world, of which a thread is part.
 *
 * <p>Running the whole row where the caller called from satisfies the second and gives up the first:
 * the same model's recursion would be held to this compile's limit in a build and to the caller's
 * stack here, so a row could be decided in one and undecided in the other. That is what this holds
 * against.
 */
class TheRowStaysOnItsWorkerAndTheApplicationDoesNotTest {

    private static final Deadline.Work WORK =
            new Deadline.Work.WholeRow("findTodo", new SourcePos(1, 1), new RowIdentity.Unnamed(1));

    /** The arrangement, on a worker of {@code stackBytes}. The wait is long enough that nothing
     *  here reaches it: what these hold is where a row and an application run, and a row given up
     *  on for time is held elsewhere. */
    private static Deadline crossing(long stackBytes) {
        return JvmDeadlines.ofMillis(Duration.ofMinutes(1).toMillis(), stackBytes);
    }

    /** The row's own work is not on the caller's thread, and what it hands over is. */
    @Test
    void theRowIsReadOnAWorkerAndTheApplicationRunsWhereItWasAskedFor() {
        AtomicReference<Thread> read = new AtomicReference<>();
        AtomicReference<Thread> applied = new AtomicReference<>();

        Deadline.Outcome<String> came = crossing(1L << 20)
                .given(WORK, () -> {
                    read.set(Thread.currentThread());
                    return (String) Handoff.onTheThreadThatAsked().call(() -> {
                        applied.set(Thread.currentThread());
                        return "answered";
                    });
                });

        assertEquals("answered", assertInstanceOf(Deadline.Outcome.Finished.class, came).value());
        assertNotEquals(Thread.currentThread(), read.get(),
                "the row is read on a worker, so its stack is this compile's answer");
        assertEquals(Thread.currentThread(), applied.get(),
                "and the application ran in the world the caller arranged");
    }

    /** The stack the row gets is the one asked for, which is what a counted depth limit needs. */
    @Test
    void theWorkerIsGivenTheStackItWasAskedFor() {
        AtomicReference<Integer> reached = new AtomicReference<>(0);

        crossing(64L << 20).given(WORK, () -> {
            reached.set(deep(0, 30_000));
            return null;
        });

        assertEquals(30_000, reached.get(),
                "a depth a default stack would not reach is reached on the worker this asks for");
    }

    private static int deep(int at, int to) {
        return at == to ? at : deep(at + 1, to);
    }

    /** What the handed-over work threw comes back as it was thrown, for the row to read. */
    @Test
    void whatTheApplicationThrewComesBackToTheRow() {
        Deadline.Outcome<String> came = crossing(1L << 20)
                .given(WORK, () -> (String) Handoff.onTheThreadThatAsked().call(() -> {
                    throw new InvocationFailure(new IllegalStateException("the SQL failed"));
                }));

        Throwable threw = assertInstanceOf(Deadline.Outcome.Threw.class, came).cause();
        assertInstanceOf(InvocationFailure.class, threw);
        assertTrue(threw.getCause() instanceof IllegalStateException);
    }

    /**
     * What an application ends with is what the row reads, and a checked one is no different.
     *
     * <p>Applying a supplied implementation is a reflective call, so what it ends with arrives as an
     * {@link InvocationTargetException} — the type the answerer reads to say the applied code came
     * back with a failure. Carried across as anything else, the same throw would be that failure
     * where a row applies where it stands and something else where it crossed.
     */
    @Test
    void aCheckedFailureCrossesAsItself() {
        InvocationTargetException stopped =
                new InvocationTargetException(new IllegalStateException("the SQL failed"));

        Deadline.Outcome<String> came = crossing(1L << 20)
                .given(WORK, () -> (String) Handoff.onTheThreadThatAsked().call(() -> {
                    throw stopped;
                }));

        assertSame(stopped, assertInstanceOf(Deadline.Outcome.Threw.class, came).cause());
    }

    /**
     * An application off a row's worker is refused rather than applied where it stands.
     *
     * <p>Applying it here would run the caller's code on a thread the caller never called from,
     * which is the one thing a crossing is for. A run that fell back to it would be deciding where
     * the caller's code runs by what its arrangement happened to install.
     */
    @Test
    void anApplicationOffARowsWorkerIsRefused() {
        assertThrows(IllegalStateException.class,
                () -> Handoff.onTheThreadThatAsked().call(() -> "applied where it stood"));
    }

    /** A row that hands nothing over still finishes, which is every run a compile makes. */
    @Test
    void aRowThatHandsNothingOverIsAnsweredAllTheSame() {
        Deadline.Outcome<String> came = crossing(1L << 20)
                .given(WORK, () -> "nothing crossed");

        assertEquals("nothing crossed",
                assertInstanceOf(Deadline.Outcome.Finished.class, came).value());
    }
}
