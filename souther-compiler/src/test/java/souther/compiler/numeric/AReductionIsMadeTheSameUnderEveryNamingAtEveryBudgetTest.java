package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many reductions a set of equalities is made into, and how many rules each is, does not turn on
 * what the positions are called, at every amount of work a way of solving it may spend. The work is
 * charged by the width of what is solved and updated and not by the weights done before one failed,
 * so a way that is cut short is cut short at the same budget under every naming.
 */
class AReductionIsMadeTheSameUnderEveryNamingAtEveryBudgetTest {

    private static final int ATOMS = 4;

    private static final ExactRatio[] WEIGHTS = {
            ExactRatio.ONE, ExactRatio.of(2), ExactRatio.of(-3), ExactRatio.of(-1)};

    private record Row(Map<Integer, ExactRatio> weights, int at, boolean equality) {}

    private static Row random(Random random, boolean equality) {
        Map<Integer, ExactRatio> weights = new LinkedHashMap<>();
        for (int i = 0, size = 2 + random.nextInt(3); i < size; i++) {
            weights.put(random.nextInt(ATOMS), WEIGHTS[random.nextInt(WEIGHTS.length)]);
        }
        return new Row(weights, random.nextInt(5) - 2, equality);
    }

    private static List<AffineConstraint<String>> constraints(List<Row> rows, String[] names) {
        List<AffineConstraint<String>> out = new ArrayList<>();
        for (Row row : rows) {
            Map<String, ExactRatio> coefs = new LinkedHashMap<>();
            row.weights().forEach((atom, weight) -> coefs.put(names[atom], weight));
            CanonicalForm<String> form = new CanonicalForm<>(coefs);
            out.add(row.equality()
                    ? new AffineConstraint.Equality<>(form, ExactRatio.of(row.at()))
                    : new AffineConstraint.HalfSpace<>(form,
                            ExactCut.inclusive(ExactRatio.of(row.at()))));
        }
        return out;
    }

    private static List<Integer> made(List<Row> rows, String[] names, int budget) {
        List<ReducedRules<String>> each = ReducedRules.of(constraints(rows, names),
                CanonicalOrder.asTheyAreSpelled(), budget);
        List<Integer> out = new ArrayList<>();
        out.add(each.size());
        each.forEach(one -> out.add(one.rules().size()));
        Collections.sort(out.subList(1, out.size()));
        return out;
    }

    @Test
    void theReductionsAreTheSameWhateverThePositionsAreCalledAtEveryBudget() {
        Random random = new Random(71);
        List<String> moved = new ArrayList<>();
        int differing = 0;
        int bound = 0;
        for (int round = 0; round < 300; round++) {
            List<Row> rows = new ArrayList<>();
            for (int i = 0, size = 1 + random.nextInt(3); i < size; i++) {
                rows.add(random(random, true));
            }
            rows.add(random(random, false));
            List<String> spelled = new ArrayList<>();
            for (int i = 0; i < ATOMS; i++) {
                spelled.add("n" + i);
            }
            List<String> shuffled = new ArrayList<>(spelled);
            Collections.shuffle(shuffled, random);
            if (!made(rows, spelled.toArray(new String[0]), 0)
                    .equals(made(rows, spelled.toArray(new String[0]), 40))) {
                bound++;
            }
            for (int budget = 0; budget <= 40; budget++) {
                List<Integer> one = made(rows, spelled.toArray(new String[0]), budget);
                List<Integer> other = made(rows, shuffled.toArray(new String[0]), budget);
                if (!one.equals(other)) {
                    differing++;
                    if (moved.size() < 3) {
                        moved.add("budget " + budget + " makes " + one + " and " + other + " of "
                                + rows);
                    }
                }
            }
        }
        assertEquals(List.of(), moved, differing + " budgets are made differently");
        assertTrue(bound > 0, "no budget changed what was made, so none was held to the names");
    }
}
