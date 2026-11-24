package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;

import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

/**
 * A conjunction, disjunction or statement on an application made equal to one still held is that
 * one, so comparing the two stops at it — and equality is still what it was.
 *
 * <p>Held three ways: made twice in a row, made at once by readers on several threads, and let go.
 * A table keeping what it hands out alive would answer the first two and never the third.
 */
class AnEqualStatementMadeAgainIsTheOneAlreadyHeldTest {

    private static Proposition truth(String at, boolean holds) {
        return new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of(at)), holds);
    }

    /** A statement no other test makes, so what is held is this test's alone. */
    private static Proposition statement(String tag) {
        return Proposition.any(List.of(
                Proposition.all(List.of(truth(tag + ".a", true), truth(tag + ".b", true))),
                Proposition.all(List.of(truth(tag + ".a", false), truth(tag + ".c", true)))));
    }

    @Test
    void madeTwiceItIsOneObject() {
        Proposition first = statement("twice");
        Proposition again = statement("twice");

        assertSame(first, again);
        Proposition part =
                Proposition.all(List.of(truth("twice.b", true), truth("twice.a", true)));
        Proposition.Any any = (Proposition.Any) first;
        assertSame(any.parts().stream().filter(part::equals).findFirst().orElseThrow(), part,
                "a part made again on its own, its parts in another order, is the part held");
    }

    @Test
    void madeOtherwiseItIsEqualAndAnotherObject() {
        Proposition shared = statement("otherwise");
        Proposition.Any any = (Proposition.Any) shared;
        Proposition built = new Proposition.Any(any.parts());

        assertEquals(shared, built, "what equality says is not what sharing says");
        assertNotSame(shared, built);
    }

    @Test
    void madeOnSeveralThreadsAtOnceItIsOneObject() throws Exception {
        ExecutorService readers = Executors.newFixedThreadPool(8);
        try {
            List<Future<Proposition>> made = new ArrayList<>();
            for (int each = 0; each < 64; each++) {
                made.add(readers.submit(() -> statement("threads")));
            }
            Proposition first = made.getFirst().get();
            for (Future<Proposition> each : made) {
                assertSame(first, each.get());
            }
        } finally {
            readers.shutdownNow();
        }
    }

    /**
     * Held by nobody, it is let go, and one made afterwards is made anew and still equal.
     *
     * <p>Whether a collection runs is the virtual machine's to decide and not something a test can
     * ask for, so a run in which none let it go says nothing either way and is set aside rather
     * than failed. A run in which one did says the table held it no more strongly than nobody did.
     */
    @Test
    void heldByNobodyItIsLetGo() {
        WeakReference<Proposition> held = new WeakReference<>(statement("let go"));
        String key = held.get().spelledOut();
        for (int tries = 0; tries < 50 && held.get() != null; tries++) {
            System.gc();
        }

        assumeTrue(held.get() == null, "no collection let anything go in this run");
        assertEquals(key, statement("let go").spelledOut());
    }
}
