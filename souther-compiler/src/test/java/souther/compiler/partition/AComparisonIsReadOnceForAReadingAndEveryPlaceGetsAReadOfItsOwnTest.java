package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.Case;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;

/**
 * What a comparison asks of a row is worked out once for a reading, and each place that asks is
 * handed a read of its own.
 */
class AComparisonIsReadOnceForAReadingAndEveryPlaceGetsAReadOfItsOwnTest {

    private static Proposition.Compared above(long value, boolean holds) {
        return new Proposition.Compared(new Relation.Affine(new LinearForm<>(
                ExactRatio.of(-value), Map.of(new DecisionAtom.OfTheInput(
                        new NumericTerm.ValueOf(TermPath.of("month"))), ExactRatio.ONE)), Rel.GT),
                holds);
    }

    private static DemandReading.Read settled(boolean thisWay) {
        return new DemandReading.Read.Settled(thisWay);
    }

    @Test
    void aComparisonIsWorkedOutOnceAndEachAskGetsAnEqualReadThatIsNotTheSame() {
        RelationsAsked asked = new RelationsAsked();
        AtomicInteger worked = new AtomicInteger();

        DemandReading.Read first = asked.of(above(3, true), () -> {
            worked.incrementAndGet();
            return settled(true);
        });
        DemandReading.Read second = asked.of(above(3, true), () -> {
            worked.incrementAndGet();
            return settled(true);
        });
        DemandReading.Read third = asked.of(above(3, true), () -> {
            worked.incrementAndGet();
            return settled(true);
        });

        assertEquals(1, worked.get());
        assertEquals(first, second);
        assertEquals(first, third);
        assertNotSame(first, second);
        assertNotSame(second, third);
        assertNotSame(first, third);
    }

    @Test
    void aComparisonHeldAndFailingOrOverAnotherValueIsWorkedOutAgain() {
        RelationsAsked asked = new RelationsAsked();
        AtomicInteger worked = new AtomicInteger();

        for (Proposition.Compared each : List.of(above(3, true), above(3, false), above(4, true))) {
            asked.of(each, () -> {
                worked.incrementAndGet();
                return settled(true);
            });
        }

        assertEquals(3, worked.get());
    }

    @Test
    void whatTheWorkSaidIsWhatEveryAskIsToldWhetherItIsKeptOrNot() {
        RelationsAsked asked = new RelationsAsked();
        Proposition.Compared compared = above(3, true);

        assertEquals(settled(false), asked.of(compared, () -> settled(false)));
        assertEquals(settled(false), asked.of(compared, () -> settled(true)));
    }

    @Test
    void aReadOfAKindThatIsNotMadeAgainFromItsPartsIsWorkedOutEveryTime() {
        RelationsAsked asked = new RelationsAsked();
        AtomicInteger worked = new AtomicInteger();
        Proposition.Compared compared = above(3, true);

        DemandReading.Read first = asked.of(compared, () -> narrows(worked));
        DemandReading.Read second = asked.of(compared, () -> narrows(worked));

        assertEquals(2, worked.get());
        assertNotSame(first, second);
    }

    @Test
    void manyThreadsAskingTogetherWorkTheComparisonOutOnce() throws Exception {
        RelationsAsked asked = new RelationsAsked();
        AtomicInteger worked = new AtomicInteger();
        int threads = 8;
        CountDownLatch started = new CountDownLatch(threads);
        ExecutorService pool = Executors.newFixedThreadPool(threads);
        try {
            List<Future<DemandReading.Read>> told = new ArrayList<>();
            for (int thread = 0; thread < threads; thread++) {
                told.add(pool.submit(() -> {
                    started.countDown();
                    started.await();
                    return asked.of(above(3, true), () -> {
                        worked.incrementAndGet();
                        // Held until the others have had the chance to come in, which they do
                        // together where nothing keeps them out.
                        sleep(100);
                        return settled(true);
                    });
                }));
            }
            Set<DemandReading.Read> distinct = Collections.newSetFromMap(new IdentityHashMap<>());
            for (Future<DemandReading.Read> each : told) {
                assertEquals(settled(true), each.get());
                distinct.add(each.get());
            }
            assertEquals(1, worked.get());
            assertEquals(threads, distinct.size());
        } finally {
            pool.shutdownNow();
        }
    }

    @Test
    void workingOneComparisonOutMayAskForAnotherOfTheSameReading() {
        RelationsAsked asked = new RelationsAsked();
        AtomicInteger worked = new AtomicInteger();

        DemandReading.Read outer = asked.of(above(3, true), () -> {
            worked.incrementAndGet();
            assertEquals(settled(false), asked.of(above(4, true), () -> {
                worked.incrementAndGet();
                return settled(false);
            }));
            return settled(true);
        });

        assertEquals(settled(true), outer);
        assertEquals(2, worked.get());
        assertEquals(settled(false), asked.of(above(4, true), () -> settled(true)));
        assertEquals(2, worked.get());
    }

    private static void sleep(long millis) {
        try {
            Thread.sleep(millis);
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
            throw new IllegalStateException(interrupted);
        }
    }

    private static DemandReading.Read narrows(AtomicInteger worked) {
        worked.incrementAndGet();
        return new DemandReading.Read.Narrows(TermPath.of("month"),
                CasesLeft.of(Refinement.of(new Case.Presence(true))));
    }
}
