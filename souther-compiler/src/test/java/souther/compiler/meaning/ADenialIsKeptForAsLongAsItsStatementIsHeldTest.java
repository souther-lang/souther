package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import java.lang.ref.WeakReference;
import java.lang.reflect.Constructor;
import java.lang.reflect.RecordComponent;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.BrokenBarrierException;
import java.util.concurrent.CyclicBarrier;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

/**
 * The denial a proposition keeps ({@link Proposition.Denial}) is made once and kept while the
 * proposition is held, the two are let go together, and keeping it changes nothing a proposition
 * is.
 *
 * <p>Asked of every kind that keeps one, each made here from parts no other test makes, so what is
 * held is this test's alone.
 */
class ADenialIsKeptForAsLongAsItsStatementIsHeldTest {

    /** One of every kind that keeps a denial, made from parts named by {@code tag}. */
    private static Map<Class<?>, Function<String, Proposition>> kinds() {
        Map<Class<?>, Function<String, Proposition>> out = new LinkedHashMap<>();
        out.put(Proposition.Compared.class, tag -> CompoundSamples.numberAtLeastZero(tag + ".n"));
        out.put(Proposition.All.class, tag -> new Proposition.All(
                List.of(CompoundSamples.truth(tag + ".a"), CompoundSamples.truth(tag + ".b"))));
        out.put(Proposition.Any.class, tag -> new Proposition.Any(
                List.of(CompoundSamples.truth(tag + ".a"), CompoundSamples.truth(tag + ".b"))));
        out.put(Proposition.OnAnApplication.class, tag -> new Proposition.OnAnApplication(
                List.of(CompoundSamples.truth(tag + ".a"), CompoundSamples.truth(tag + ".b"))));
        out.put(Proposition.SoManyHold.class, tag -> CompoundSamples.holding(
                Proposition.SoManyHold.class, CompoundSamples.truth(tag + ".a"),
                CompoundSamples.truth(tag + ".b"), null));
        return out;
    }

    @Test
    void everyKindThatKeepsADenialIsAskedHere() {
        Set<Class<?>> keeping = new LinkedHashSet<>();
        for (Class<?> kind : Proposition.class.getPermittedSubclasses()) {
            for (RecordComponent component : kind.getRecordComponents()) {
                if (component.getType() == Proposition.Denial.class) {
                    keeping.add(kind);
                }
            }
        }
        assertEquals(keeping, kinds().keySet());
    }

    /**
     * Held by the statement and by nobody else, the denial outlives a collection, and the one
     * asked for afterwards is that one.
     */
    @Test
    void whileTheStatementIsHeldItsDenialIsTheOneMadeFirst() {
        kinds().forEach((kind, made) -> {
            Proposition stated = made.apply("held " + kind.getSimpleName());
            WeakReference<Proposition> denial = deniedAndDropped(stated);
            assumeTrue(aCollectionRan(), "no collection let anything go in this run");

            assertNotNull(denial.get(), kind.getSimpleName());
            assertSame(denial.get(), stated.denied(), kind.getSimpleName());
        });
    }

    /**
     * Held by nobody, a statement and its denial are both let go, though each holds the other
     * where the denial of the denial is the statement.
     */
    @Test
    void heldByNobodyTheStatementAndItsDenialAreLetGo() {
        kinds().forEach((kind, made) -> {
            List<WeakReference<Proposition>> both = madeAndDropped(made, kind);
            for (int tries = 0; tries < 50 && both.stream().anyMatch(it -> it.get() != null);
                 tries++) {
                System.gc();
            }
            assumeTrue(aCollectionRan(), "no collection let anything go in this run");

            assertNull(both.get(0).get(), kind.getSimpleName() + ": the statement");
            assertNull(both.get(1).get(), kind.getSimpleName() + ": its denial");
        });
    }

    /** What its denial is equal to, the denial of a statement made again is equal to as well, and
     *  one whose denial is kept is equal to, and hashes as, one whose denial was never asked. */
    @Test
    void aKeptDenialChangesNeitherEqualityNorHashing() {
        kinds().forEach((kind, made) -> {
            Proposition asked = made.apply("equal " + kind.getSimpleName());
            Proposition notAsked = made.apply("equal " + kind.getSimpleName());
            Proposition denial = asked.denied();

            assertEquals(asked, notAsked, kind.getSimpleName());
            assertEquals(notAsked, asked, kind.getSimpleName());
            assertEquals(asked.hashCode(), notAsked.hashCode(), kind.getSimpleName());
            assertEquals(denial, made.apply("equal " + kind.getSimpleName()).denied(),
                    kind.getSimpleName());
        });
    }

    /**
     * A proposition built from the components of one whose denial is kept keeps a denial of its
     * own: the cell handed in is not the one it holds, and the two are equal.
     */
    @Test
    void aTwinBuiltFromTheComponentsKeepsADenialOfItsOwn() throws Exception {
        for (Map.Entry<Class<?>, Function<String, Proposition>> each : kinds().entrySet()) {
            Class<?> kind = each.getKey();
            Proposition stated = each.getValue().apply("twin " + kind.getSimpleName());
            Proposition denial = stated.denied();
            RecordComponent[] held = kind.getRecordComponents();
            Class<?>[] types = new Class<?>[held.length];
            Object[] values = new Object[held.length];
            Object cell = null;
            for (int at = 0; at < held.length; at++) {
                types[at] = held[at].getType();
                values[at] = held[at].getAccessor().invoke(stated);
                if (types[at] == Proposition.Denial.class) {
                    cell = values[at];
                }
            }
            Constructor<?> canonical = kind.getDeclaredConstructor(types);
            Proposition twin = (Proposition) canonical.newInstance(values);

            assertEquals(stated, twin, kind.getSimpleName());
            assertNotNull(cell, kind.getSimpleName());
            for (RecordComponent component : held) {
                if (component.getType() == Proposition.Denial.class) {
                    assertNotSame(cell, component.getAccessor().invoke(twin),
                            kind.getSimpleName());
                }
            }
            assertEquals(denial, twin.denied(), kind.getSimpleName());
        }
    }

    /**
     * Readers on several threads that each made a denial before any of them kept one are all
     * handed the one kept first.
     *
     * <p>Asked of the cell with a maker that makes a new object each time and waits until every
     * reader has made one. Through a kind's own denial the question would not be asked: what a
     * kind makes is kept as the equal one already held ({@link SharedPropositions#shared}), so
     * readers handed what each made would still be handed one object.
     */
    @Test
    void readersThatEachMadeADenialAreHandedTheOneKeptFirst() throws Exception {
        int readers = 8;
        Proposition stated = CompoundSamples.truth("threads.a");
        Proposition.Denial cell = new Proposition.Denial();
        CyclicBarrier allMade = new CyclicBarrier(readers);
        ExecutorService pool = Executors.newFixedThreadPool(readers);
        try {
            List<Future<Proposition>> asked = new ArrayList<>();
            for (int reader = 0; reader < readers; reader++) {
                asked.add(pool.submit(() -> cell.of(stated, truth -> {
                    Proposition made = new Proposition.All(List.of(truth.denied(),
                            CompoundSamples.truth("threads.b")));
                    await(allMade);
                    return made;
                })));
            }
            Proposition first = asked.getFirst().get(10, TimeUnit.SECONDS);
            for (Future<Proposition> one : asked) {
                assertSame(first, one.get(10, TimeUnit.SECONDS));
            }
        } finally {
            pool.shutdownNow();
        }
    }

    private static void await(CyclicBarrier barrier) {
        try {
            barrier.await(10, TimeUnit.SECONDS);
        } catch (InterruptedException | BrokenBarrierException | TimeoutException stopped) {
            throw new IllegalStateException("the readers did not all make one", stopped);
        }
    }

    /**
     * Denied twice, a comparison is itself: denying back and forth makes one denial and no more.
     * Readers make comparisons afresh, so made afresh too, every turn would be one more
     * comparison and one more held.
     */
    @Test
    void aComparisonDeniedTwiceIsItself() {
        Proposition stated = CompoundSamples.numberAtLeastZero("twice.n");

        assertSame(stated, stated.denied().denied());
        assertSame(stated.denied(), stated.denied().denied().denied());
    }

    /** Two equal comparisons made apart share one denial: each is asked through the one kept. */
    @Test
    void equalComparisonsMadeApartShareOneDenial() {
        Proposition one = CompoundSamples.numberAtLeastZero("apart.n");
        Proposition other = CompoundSamples.numberAtLeastZero("apart.n");
        assertNotSame(one, other);

        assertSame(one.denied(), other.denied());
    }

    /**
     * What is kept is the statement's, and not the other way round: denied twice, a statement made
     * directly comes back equal and is not asked to come back as itself, while one made as the
     * equal one kept does.
     */
    @Test
    void deniedTwiceAStatementIsEqualAndItselfOnlyWhereItIsTheOneKept() {
        List<Proposition> parts =
                List.of(CompoundSamples.truth("twice.a"), CompoundSamples.truth("twice.b"));
        Proposition direct = new Proposition.All(parts);
        assertEquals(direct, direct.denied().denied());

        Proposition kept = Proposition.all(parts);
        assertSame(kept, kept.denied().denied());
        assertSame(kept, direct.denied().denied(), "the direct one's comes back as the one kept");
    }

    /** Written out, a proposition whose denial of its denial is itself is written out once. */
    @Test
    void aStatementHeldByItsOwnDenialIsWrittenOutOnce() {
        Proposition stated = Proposition.all(List.of(CompoundSamples.truth("written.a"),
                CompoundSamples.truth("written.b")));
        Proposition denial = stated.denied();
        assertSame(stated, denial.denied(), "the statement is the one kept");

        String written = stated.toString();
        assertTrue(written.contains("written.a"), written);
        assertEquals(-1, written.indexOf("any["), written);
    }

    /** The denial of {@code stated} made, and a reference to it that does not hold it. Made in a
     *  method of its own so that nothing on the caller's frame holds it. */
    private static WeakReference<Proposition> deniedAndDropped(Proposition stated) {
        return new WeakReference<>(stated.denied());
    }

    /** A statement of {@code kind} and its denial, both made and neither held. */
    private static List<WeakReference<Proposition>> madeAndDropped(
            Function<String, Proposition> made, Class<?> kind) {
        Proposition stated = made.apply("let go " + kind.getSimpleName());
        Proposition denial = stated.denied();
        denial.denied();
        return List.of(new WeakReference<>(stated), new WeakReference<>(denial));
    }

    /** Whether a collection let something nobody holds go, asked until one did or until it is
     *  plain that none will. */
    private static boolean aCollectionRan() {
        WeakReference<Object> nobodys = new WeakReference<>(new Object());
        for (int tries = 0; tries < 50 && nobodys.get() != null; tries++) {
            System.gc();
        }
        return nobodys.get() == null;
    }
}
