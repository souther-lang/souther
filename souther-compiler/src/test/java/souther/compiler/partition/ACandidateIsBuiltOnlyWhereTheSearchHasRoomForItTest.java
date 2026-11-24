package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.AbstractList;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The search tries as many candidates as its figure and takes one past it as the word that the
 * figure was passed. A producer of candidates stops building where there is no room for one more,
 * and does not build all it could and leave the cut to the end: what it costs is what the figure
 * allows, whatever the types it builds from have to offer.
 */
class ACandidateIsBuiltOnlyWhereTheSearchHasRoomForItTest {

    private static List<FixtureTemplate> numbers(int how) {
        return IntStream.range(0, how).mapToObj(FixtureTemplate::integer).toList();
    }

    @Test
    void thereIsRoomUpToTheFigureAndThenOneMoreToSayItWasPassed() {
        assertTrue(RowSearch.hasRoom(Collections.nCopies(RowSearch.MOST_VALUES, 0)));
        assertFalse(RowSearch.hasRoom(Collections.nCopies(RowSearch.MOST_VALUES + 1, 0)));
    }

    @Test
    void entriesOfHundredsOfKeysAndValuesAreMadeOnlyAsFarAsTheRoomGoes() {
        AtomicInteger valuesRead = new AtomicInteger();
        List<FixtureTemplate> values = new AbstractList<>() {
            @Override
            public FixtureTemplate get(int at) {
                valuesRead.incrementAndGet();
                return FixtureTemplate.integer(at);
            }

            @Override
            public int size() {
                return 100;
            }
        };
        List<FixtureTemplate> into = new ArrayList<>();

        RowSearch.addEachHoldingOneEntry(numbers(100), values, FixtureTemplate::collection, into);

        assertEquals(RowSearch.MOST_VALUES + 1, into.size());
        assertTrue(valuesRead.get() <= RowSearch.MOST_VALUES + 2,
                "values read: " + valuesRead.get());
    }

    @Test
    void aTypeIsAskedForTwoValuesAtLeastAndNoMoreThanOnePastTheFigure() {
        assertEquals(2, CountWitnesses.valuesAskedOfAType(0));
        assertEquals(5, CountWitnesses.valuesAskedOfAType(5));
        assertEquals(RowSearch.MOST_VALUES + 1, CountWitnesses.valuesAskedOfAType(100_000));
    }

    @Test
    void whatFitsInTheRoomIsMadeWhole() {
        List<FixtureTemplate> into = new ArrayList<>();

        RowSearch.addEachHoldingOneEntry(numbers(2), numbers(2), FixtureTemplate::collection, into);

        assertEquals(4, into.size());
    }
}
