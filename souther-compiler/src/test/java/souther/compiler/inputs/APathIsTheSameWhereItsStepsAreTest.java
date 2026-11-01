package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two paths are one where their head and their steps are, however each was made.
 *
 * <p>The steps of a path keep their own hash. What that must not change is what a path is equal to
 * and what it hashes as: a path made from a plain list and a path made by walking one field further
 * are the same path, and its steps are the list they were made from.
 */
class APathIsTheSameWhereItsStepsAreTest {

    private static final List<TermPath.Step> STEPS = List.of(
            new TermPath.Step.Field("cost"), new TermPath.Step.Element(),
            new TermPath.Step.Field("value"));

    @Test
    void pathsMadeApartFromTheSameStepsAreEqualAndHashAlike() {
        TermPath one = new TermPath("request", STEPS);
        TermPath other = new TermPath("request", new ArrayList<>(STEPS));

        assertEquals(one, other);
        assertEquals(one.hashCode(), other.hashCode());
        assertEquals(Set.of(one), new HashSet<>(List.of(other)));
    }

    @Test
    void aPathMadeByWalkingFurtherIsThePathMadeAtOnce() {
        TermPath walked = TermPath.of("request").then("cost");

        assertEquals(new TermPath("request", List.of(new TermPath.Step.Field("cost"))), walked);
        assertEquals(walked.hashCode(),
                new TermPath("request", List.of(new TermPath.Step.Field("cost"))).hashCode());
    }

    @Test
    void pathsThatDifferInAStepOrTheHeadAreNotEqual() {
        TermPath path = new TermPath("request", STEPS);

        assertNotEquals(path, new TermPath("request", STEPS.subList(0, 2)));
        assertNotEquals(path, new TermPath("other", STEPS));
        assertNotEquals(path, new TermPath("request", List.of(
                new TermPath.Step.Field("cost"), new TermPath.Step.Key(),
                new TermPath.Step.Field("value"))));
    }

    @Test
    void equalHashesDoNotMakeDifferentPathsEqual() {
        TermPath one = TermPath.of("request").then("Aa");
        TermPath other = TermPath.of("request").then("BB");

        assertEquals(one.hashCode(), other.hashCode(), "the two spellings hash alike");
        assertNotEquals(one, other);
    }

    @Test
    void stepsThatHashToNoughtAreHashedAndComparedAsTheyAre() {
        TermPath path = TermPath.of("request").then("xwhiaoxk");
        List<TermPath.Step> written = List.of(new TermPath.Step.Field("xwhiaoxk"));

        assertEquals(0, written.hashCode(), "a list that hashes to nought");
        assertEquals(0, path.steps().hashCode());
        assertEquals(0, path.steps().hashCode(), "and again");
        assertEquals(new TermPath("request", written), path);
        assertNotEquals(TermPath.of("request").then("other"), path);
    }

    @Test
    void aPathDerivedAgainByTheSameStepIsTheSameInstance() {
        TermPath root = TermPath.of("request");

        assertSame(root, TermPath.of("request"));
        assertSame(root.then("cost"), root.then("cost"));
        assertSame(root.element(), root.element());
        assertSame(root.key(), root.key());
        assertNotSame(root.element(), root.key());
        assertSame(root.then("cost").element().then("value"),
                root.then(List.of("cost")).element().then(List.of("value")));
    }

    @Test
    void aPathReachedBySeveralDerivationsIsOneInstance() {
        TermPath path = TermPath.of("request").then("cost").element().then("value");

        assertSame(path, TermPath.of("request", STEPS));
        assertSame(path, TermPath.of("other").then("cost").element().then("value")
                .movedFrom(TermPath.of("other"), TermPath.of("request")));
        assertSame(path, path.then("deeper").prefix(3));
        assertSame(path, TermPath.of("request").then(List.of("cost")).element().then("value"));
        assertSame(path, TermPath.of("x").then("y").under(TermPath.of("request").then("cost")
                .element()).movedFrom(TermPath.of("request").then("cost").element().then("y"),
                TermPath.of("request").then("cost").element()).then("value").prefix(3));
        assertSame(path.prefix(2), path.outermostContainer().element());
    }

    @Test
    void aPathMadeByTheConstructorIsEqualToTheOneDerivedAndDerivesFromIt() {
        TermPath derived = TermPath.of("request").then("cost").element().then("value");
        TermPath written = new TermPath("request", new ArrayList<>(STEPS));

        assertNotSame(derived, written);
        assertEquals(derived, written);
        assertEquals(derived.hashCode(), written.hashCode());
        assertSame(derived.then("more"), written.then("more"));
        assertSame(derived.prefix(1), written.prefix(1));
    }

    @Test
    void pathsOfDifferentHeadsDoNotShareWhatIsDerived() {
        TermPath one = TermPath.of("one").then("cost");
        TermPath other = new TermPath("other", one.steps()).then("price");

        assertEquals("one.cost", one.toString());
        assertEquals("other.cost.price", other.toString());
        assertEquals("one.cost.price", one.then("price").toString());
        assertNotEquals(one, other);
    }

    /**
     * A path nothing holds is not kept by the table that finds paths again, and neither is what it
     * was derived from: one table serves every compile a process makes, and a parent kept for the
     * sake of a child that is gone would keep every path of that compile with it.
     */
    @Test
    void pathsNothingHoldsAreLetGoOfWithTheirParentsAndRoots() throws InterruptedException {
        List<WeakReference<TermPath>> watched = new ArrayList<>();
        TermPath root = TermPath.of("gone-root");
        watched.add(new WeakReference<>(root));
        TermPath path = root.then("a").element().then("b");
        for (TermPath at = path; at.steps().size() > 0; at = at.prefix(at.steps().size() - 1)) {
            watched.add(new WeakReference<>(at));
        }
        root = null;
        path = null;

        for (int asked = 0; asked < 50 && watched.stream().anyMatch(each -> each.get() != null);
             asked++) {
            System.gc();
            Thread.sleep(10);
        }

        assertTrue(watched.stream().allMatch(each -> each.get() == null),
                "a path, or something it was derived from, is still held by the table");
    }

    /** What the table files is let go of too: a table that kept a name or a step for every path
     *  ever made would grow with the models a process reads. */
    @Test
    void whatTheTableFilesForPathsLetGoOfIsLetGoOfAsWell() throws InterruptedException {
        int before = TermPath.placesFiled();
        for (int round = 0; round < 200; round++) {
            TermPath.of("name-" + round).then("a").element().then("b");
        }
        assertTrue(TermPath.placesFiled() > before, "the paths made are filed while they are held");
        for (int asked = 0; asked < 20 && TermPath.placesFiled() > before; asked++) {
            System.gc();
            Thread.sleep(10);
        }

        assertTrue(TermPath.placesFiled() <= before,
                "the table files " + (TermPath.placesFiled() - before)
                        + " places more than it did, for paths nothing holds");
    }

    /** Threads deriving the same places at once end up holding one instance of each. */
    @Test
    void threadsDerivingTheSamePlacesAtOnceAreHandedOneInstanceOfEach() throws Exception {
        int threads = 8;
        TermPath root = TermPath.of("shared");
        ExecutorService pool = Executors.newFixedThreadPool(threads);
        try {
            CountDownLatch together = new CountDownLatch(threads);
            List<Future<List<TermPath>>> made = new ArrayList<>();
            for (int t = 0; t < threads; t++) {
                made.add(pool.submit(() -> {
                    together.countDown();
                    together.await();
                    List<TermPath> out = new ArrayList<>();
                    for (int i = 0; i < 200; i++) {
                        out.add(root.then("f" + i).element().then("g"));
                    }
                    return out;
                }));
            }
            List<TermPath> first = made.getFirst().get();
            for (Future<List<TermPath>> each : made) {
                List<TermPath> other = each.get();
                for (int i = 0; i < first.size(); i++) {
                    assertSame(first.get(i), other.get(i));
                }
            }
        } finally {
            pool.shutdownNow();
        }
    }

    @Test
    void theStepsAreTheListTheyWereMadeFromAndCannotBeChanged() {
        TermPath path = new TermPath("request", STEPS);

        assertEquals(STEPS, path.steps());
        assertEquals(path.steps(), STEPS);
        assertEquals(STEPS.hashCode(), path.steps().hashCode());
        assertTrue(path.steps() instanceof java.util.RandomAccess);
        assertThrows(UnsupportedOperationException.class,
                () -> path.steps().add(new TermPath.Step.Element()));
    }
}
