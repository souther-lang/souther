package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How often each of several keys occurs is tried for every combination, and the combinations
 * multiply with the keys. A walk that builds nothing is stopped by neither the leaves nor the
 * containers offered, which count what was built, so it is held to a figure that counts what was
 * tried.
 */
class TheCountsOfSeveralKeysTriedAreHeldToAFigureOfTheirOwnTest {

    private static final int MOST = CompositionBudget.COUNTS_OF_KEYS_TRIED.maximum();

    private static TermRealizations.Realization nothingComposes() {
        return new TermRealizations.Realization.None(
                Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE, "nothing composes");
    }

    /** Keys the rules leave any count of, over containers that hold none of the combinations. */
    @Test
    void manyKeysThatNoContainerHoldsAreStoppedAtTheFigureAndSaySo() {
        List<Place> values = new ArrayList<>();
        List<List<NumericSet>> wanted = new ArrayList<>();
        for (int i = 0; i < 16; i++) {
            values.add(Count.of(i));
            wanted.add(List.of(new NumericSet.AwayFrom(List.of(Count.of(-1)))));
        }
        AtomicInteger composed = new AtomicInteger();
        CardinalityComposer.ValuesCountedFor search = new CardinalityComposer.ValuesCountedFor(
                values, wanted, NumericDomain.Bounds.OPEN, List.of(Count.of(100)),
                (counted, others, room) -> {
                    composed.incrementAndGet();
                    return nothingComposes();
                });

        search.counting(0, new ArrayList<>(), 0);

        assertTrue(search.spent, "the walk is cut at the figure, and is said to be");
        assertTrue(composed.get() <= MOST, () -> composed + " containers composed past " + MOST);
        assertTrue(search.built.isEmpty());
    }

    /** Combinations that lead nowhere are counted as well as the ones composed. */
    @Test
    void combinationsThatEndBeforeAnyIsComposedAreCountedToo() {
        List<Place> values = new ArrayList<>();
        List<List<NumericSet>> wanted = new ArrayList<>();
        for (int i = 0; i < 15; i++) {
            values.add(Count.of(i));
            wanted.add(List.of(new NumericSet.AwayFrom(List.of(Count.of(-1)))));
        }
        // A last key no count of is asked: every combination of the others dies at it.
        values.add(Count.of(15));
        wanted.add(List.of(new NumericSet.At(Count.of(-1))));
        AtomicInteger composed = new AtomicInteger();
        CardinalityComposer.ValuesCountedFor search = new CardinalityComposer.ValuesCountedFor(
                values, wanted, NumericDomain.Bounds.OPEN, List.of(),
                (counted, others, room) -> {
                    composed.incrementAndGet();
                    return nothingComposes();
                });

        search.counting(0, new ArrayList<>(), 0);

        assertEquals(0, composed.get());
        assertTrue(search.spent, "the walk is cut at the figure, and is said to be");
        assertTrue(search.tried <= MOST + 1, () -> search.tried + " tried past " + MOST);
    }

    /** A few keys are walked to the end, and the figure is not said to have been reached. */
    @Test
    void fewKeysAreWalkedToTheEndAndTheFigureIsNotSaidToHaveStoppedThem() {
        List<Place> values = List.of(Count.of(1), Count.of(2));
        List<List<NumericSet>> wanted = List.of(List.of(new NumericSet.At(Count.of(3))),
                List.of(new NumericSet.At(Count.of(0))));
        AtomicInteger composed = new AtomicInteger();
        CardinalityComposer.ValuesCountedFor search = new CardinalityComposer.ValuesCountedFor(
                values, wanted, NumericDomain.Bounds.OPEN, List.of(),
                (counted, others, room) -> {
                    composed.incrementAndGet();
                    return nothingComposes();
                });

        search.counting(0, new ArrayList<>(), 0);

        assertFalse(search.spent);
        assertEquals(1, composed.get(), "the one combination the counts asked");
    }
}
