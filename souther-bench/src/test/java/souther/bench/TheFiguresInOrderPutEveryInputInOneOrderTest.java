package souther.bench;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.Figure;
import souther.compiler.observe.WorkFigure;
import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * {@link Figure#inOrder} is a crossing the reading trusts, so no two figures that differ are tied by it.
 *
 * <p>It sorts by name and then by what the figure stood at, and a stable sort leaves what it ties
 * in the order the walk gave. The reading takes it as putting a plurality in one order, which holds
 * only while that pair tells every two figures apart; a figure added later whose name and
 * standing another already has would make it false without any test of the figures saying so.
 *
 * <p>The population is every figure of both kinds, and at more than one standing for the ones
 * that are handed one, including standings spelled alike.
 */
class TheFiguresInOrderPutEveryInputInOneOrderTest {

    @Test
    void noTwoFiguresThatDifferShareANameAndAStanding() {
        List<Figure> population = population();
        assertFalse(population.isEmpty(), "there are no figures to ask");

        Map<String, Figure> byKey = new LinkedHashMap<>();
        List<String> tied = new ArrayList<>();
        for (Figure each : population) {
            Figure other = byKey.putIfAbsent(each.name() + "\u0000" + each.most(), each);
            if (other != null && !other.equals(each)) {
                tied.add(other + " and " + each);
            }
        }

        assertEquals(List.of(), tied,
                "two figures that differ are tied by the order figures are put in, so a stable"
                        + " sort leaves them as the walk gave them");
    }

    @Test
    void theSameFiguresComeOutInTheSameOrderWhateverOrderTheyWereGivenIn() {
        List<Figure> population = population();
        List<Figure> expected = Figure.inOrder(population);
        assertEquals(new HashSet<>(population).size(), expected.size(),
                "figures that differ were taken for one");

        Random random = new Random(7);
        for (int round = 0; round < 20; round++) {
            List<Figure> shuffled = new ArrayList<>(population);
            Collections.shuffle(shuffled, random);
            assertEquals(expected, Figure.inOrder(shuffled),
                    "the figures came out in an order that depends on the order they went in");
        }
    }

    private static List<Figure> population() {
        List<Figure> out = new ArrayList<>();
        for (CompositionBudget each : CompositionBudget.values()) {
            out.add(new Figure.Budget(each));
        }
        for (WorkFigure each : WorkFigure.values()) {
            for (String standing : Set.of("0", "1", "01", "10", "9", "")) {
                out.add(each.at(standing));
            }
        }
        return out;
    }
}
