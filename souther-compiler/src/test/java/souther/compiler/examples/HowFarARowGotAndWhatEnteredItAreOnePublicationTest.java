package souther.compiler.examples;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.Applied;
import souther.compiler.observe.Stage;

import java.util.concurrent.atomic.AtomicBoolean;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A row still running is read from another thread, and what it says about itself is read whole.
 *
 * <p>How far a row got and what entered the behavior are one fact: everything at
 * {@link Stage#INVOKED} says what applied it, and {@code RowOutcome} refuses to be built from a pair
 * that says otherwise. Published as two, a reader can take the first from before the row took back
 * having entered and the second from after, and hold a pair no moment of the evaluation ever had —
 * which reaches the reader that gives up on a row as a build that fails on a timing window.
 *
 * <p>So the two are one field, and what this holds is that they stay one. Split again, the reader
 * below sees a stage that says a behavior was entered with nothing that entered it.
 */
class HowFarARowGotAndWhatEnteredItAreOnePublicationTest {

    /** Long enough that a split publication is read mid-flight, short enough to stay a unit test. */
    private static final int ROUNDS = 200_000;

    @Test
    void aRowThatTakesBackHavingEnteredIsNeverReadHalfWay() throws InterruptedException {
        ExampleVerifier.RowState state = new ExampleVerifier.RowState();
        AtomicBoolean torn = new AtomicBoolean();
        AtomicBoolean done = new AtomicBoolean();

        Thread reader = new Thread(() -> {
            while (!done.get()) {
                ExampleVerifier.Reached read = state.reached;
                if (read.stage().reached(Stage.INVOKED) != (read.applied() != null)) {
                    torn.set(true);
                    return;
                }
            }
        });
        reader.setDaemon(true);
        reader.start();

        // What a row does when its answerer comes back saying it never got in: enter, then take it
        // back. The two writes are the ones a reader can fall between.
        for (int i = 0; i < ROUNDS; i++) {
            state.entered(new Applied.GeneratedHere());
            state.neverEntered();
        }
        done.set(true);
        reader.join();

        assertEquals(false, torn.get(),
                "a reader of a row still running never sees a stage that says the behavior was"
                        + " entered with nothing that entered it");
    }
}
