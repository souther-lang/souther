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
 * What a set of equalities is read as, at every amount of work it may be given, does not turn on
 * what the positions are called. The work a reading may spend is bounded, and a bound met in an
 * order the names decide makes what is shown a function of the names: the one place that shows is
 * the edge of the work, so it is the edge that is held, one budget at a time, and not only a budget
 * far past what any of these needs.
 *
 * <p>The weights are of sizes whose quotients are not all held, which is what makes some position
 * of an equality unable to be solved for, and the equalities are of widths and shapes that make the
 * number of weights updated differ with which position each is solved for.
 */
class AnEqualitySpanIsReadTheSameUnderEveryNamingAtEveryBudgetTest {

    private static final int ATOMS = 5;

    private static final ExactRatio[] WEIGHTS = {
            ExactRatio.ONE, ExactRatio.of(2), ExactRatio.of(-3),
            ExactRatio.tenTo(Long.MIN_VALUE), ExactRatio.tenTo(Long.MAX_VALUE)};

    private record Row(Map<Integer, ExactRatio> weights, int at) {}

    private static Row random(Random random, int sizes) {
        Map<Integer, ExactRatio> weights = new LinkedHashMap<>();
        for (int i = 0, size = 2 + random.nextInt(3); i < size; i++) {
            weights.put(random.nextInt(ATOMS), WEIGHTS[random.nextInt(sizes)]);
        }
        return new Row(weights, random.nextInt(5) - 2);
    }

    private static AffineConstraint<String> constraint(Row row, String[] names) {
        Map<String, ExactRatio> coefs = new LinkedHashMap<>();
        row.weights().forEach((atom, weight) -> coefs.put(names[atom], weight));
        return new AffineConstraint.Equality<>(new CanonicalForm<>(coefs), ExactRatio.of(row.at()));
    }

    /** What the span shows of the equalities themselves: for each, whether it comes to nothing once
     *  the span is taken out of it, and whether the span was made at all. */
    private static List<Boolean> shown(List<Row> rows, String[] names, int budget) {
        List<AffineConstraint<String>> rules = new ArrayList<>();
        rows.forEach(row -> rules.add(constraint(row, names)));
        EqualitySpan<String> span =
                EqualitySpan.of(rules, CanonicalOrder.asTheyAreSpelled(), budget);
        List<Boolean> out = new ArrayList<>();
        out.add(span != null);
        if (span == null) {
            return out;
        }
        for (AffineConstraint<String> each : rules) {
            AffineConstraint.Equality<String> equality = (AffineConstraint.Equality<String>) each;
            Map<String, ExactRatio> coefs = new LinkedHashMap<>();
            equality.form().entriesIn(CanonicalOrder.asTheyAreSpelled())
                    .forEach(entry -> coefs.put(entry.getKey(), entry.getValue()));
            EqualitySpan.Residue<String> left = span.residue(new CanonicalForm<>(coefs),
                    equality.at().negated());
            out.add(left != null && left.coefs().isEmpty() && left.constant().isZero());
        }
        return out;
    }

    private static String[] called(Random random, boolean spelled) {
        List<String> names = new ArrayList<>();
        for (int i = 0; i < ATOMS; i++) {
            names.add("n" + i);
        }
        if (!spelled) {
            Collections.shuffle(names, random);
        }
        return names.toArray(new String[0]);
    }

    /** Weights whose quotients are all held. */
    @Test
    void whatIsReadIsTheSameWhateverThePositionsAreCalledAtEveryBudget() {
        assertTheSameAtEveryBudget(3, 61);
    }

    /** And where some weights are too far apart in size for their quotients to be held. */
    @Test
    void whatIsReadIsTheSameWhateverThePositionsAreCalledWhereSomeQuotientsAreNotHeld() {
        assertTheSameAtEveryBudget(WEIGHTS.length, 67);
    }

    private static void assertTheSameAtEveryBudget(int sizes, long seed) {
        Random random = new Random(seed);
        List<String> moved = new ArrayList<>();
        int differing = 0;
        for (int round = 0; round < 300; round++) {
            List<Row> rows = new ArrayList<>();
            for (int i = 0, size = 1 + random.nextInt(4); i < size; i++) {
                rows.add(random(random, sizes));
            }
            String[] one = called(random, true);
            String[] other = called(random, false);
            for (int budget = 0; budget <= 60; budget++) {
                if (!shown(rows, one, budget).equals(shown(rows, other, budget))) {
                    differing++;
                    if (moved.size() < 3) {
                        moved.add("budget " + budget + " reads " + shown(rows, one, budget)
                                + " and " + shown(rows, other, budget) + " of " + rows);
                    }
                }
            }
        }
        assertEquals(List.of(), moved, differing + " budgets are read differently");
        assertTrue(true);
    }
}
