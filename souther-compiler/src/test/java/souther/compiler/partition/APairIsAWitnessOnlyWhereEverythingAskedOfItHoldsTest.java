package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.Figure;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A pair is a witness only where everything asked of it holds of it together, and one that fails
 * any part is no reason to look at no other. Asked of the search of the pairs alone, with what is
 * asked of a pair — the container holding it, a run of its row getting to the comparison — as one
 * question over the pair: a part that fails the first pairs and holds of a later one still finds
 * it, the figure the elements are tried to stops the asking and says so, and a search that stopped
 * is no search that found none.
 */
class APairIsAWitnessOnlyWhereEverythingAskedOfItHoldsTest {

    @Test
    void aPairOfTheFirstOfEachIsNotTheOnlyOneAsked() {
        List<List<Integer>> asked = new ArrayList<>();
        List<Integer> found = CountWitnesses.firstPairThat(List.of(1, 2, 3), List.of(10, 20),
                false, pair -> {
                    asked.add(pair);
                    return pair.equals(List.of(2, 20));
                }, new LinkedHashSet<>());
        assertEquals(List.of(2, 20), found);
        assertEquals(List.of(List.of(1, 10), List.of(1, 20), List.of(2, 10), List.of(2, 20)),
                asked, "in the order the elements were tried, and no further than the one found");
    }

    @Test
    void twoOfOneListAreAskedEarlierFirstAndNeverWithThemselves() {
        List<List<Integer>> asked = new ArrayList<>();
        assertNull(CountWitnesses.firstPairThat(List.of(1, 2, 3), List.of(1, 2, 3), true,
                pair -> {
                    asked.add(pair);
                    return false;
                }, new LinkedHashSet<>()));
        assertEquals(List.of(List.of(1, 2), List.of(1, 3), List.of(2, 3)), asked);
    }

    @Test
    void thePairsAreAskedUpToTheFigureAndTheFigureIsSaid() {
        Set<Figure> stopped = new LinkedHashSet<>();
        List<Integer> many = new ArrayList<>();
        for (int each = 0; each < 40; each++) {
            many.add(each);
        }
        int[] asked = {0};
        assertNull(CountWitnesses.firstPairThat(many, many, false, _ -> {
            asked[0]++;
            return false;
        }, stopped));
        assertEquals(RowSearch.MOST_VALUES, asked[0]);
        assertEquals(Set.of(CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG.figure()),
                stopped);
    }

    @Test
    void aSearchThatAskedEveryPairSaysNoFigure() {
        Set<Figure> stopped = new LinkedHashSet<>();
        assertNull(CountWitnesses.firstPairThat(List.of(1, 2), List.of(3, 4), false, _ -> false,
                stopped));
        assertTrue(stopped.isEmpty(), "every pair was asked, and none holds");
    }
}
