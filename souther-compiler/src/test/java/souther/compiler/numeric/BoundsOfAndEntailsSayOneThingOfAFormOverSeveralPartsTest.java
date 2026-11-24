package souther.compiler.numeric;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.math.BigDecimal;
import java.math.RoundingMode;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import org.junit.jupiter.api.Test;
import souther.compiler.numeric.NumericDomain.Bounds;

/**
 * How high a form comes to is one statement whoever asks it: the highest {@code boundsOf} reports
 * is the lowest bound {@code entails} proves, for a form over positions of two parts of the rules
 * that no rule joins — which is where the parts are asked for their own share of the form.
 */
class BoundsOfAndEntailsSayOneThingOfAFormOverSeveralPartsTest {

    private static final List<String> LEFT = List.of("a", "b", "c");
    private static final List<String> RIGHT = List.of("x", "y", "z");

    private static Map<String, NumberSpace> spaces() {
        Map<String, NumberSpace> out = new LinkedHashMap<>();
        for (String atom : List.of("a", "b", "c", "x", "y", "z")) {
            out.put(atom, NumberSpace.spacedOnly(Granularity.DISCRETE));
        }
        return out;
    }

    private static LinearForm<String> form(Map<String, Integer> weights, long constant) {
        Map<String, ExactRatio> coefs = new LinkedHashMap<>();
        weights.forEach((atom, weight) -> coefs.put(atom, ExactRatio.of(weight)));
        return new LinearForm<>(ExactRatio.of(constant), coefs);
    }

    @Test
    void theHighestReportedIsTheLowestBoundProven() {
        Random dice = new Random(3210);
        int asked = 0;
        for (int round = 0; round < 3000; round++) {
            NumericDomain<String> domain = NumericDomain.top(CanonicalOrder.asTheyAreSpelled(),
                    ClosedStates.kept());
            for (List<String> atoms : List.of(LEFT, RIGHT)) {
                int rules = 2 + dice.nextInt(4);
                for (int each = 0; each < rules; each++) {
                    Map<String, Integer> weights = new LinkedHashMap<>();
                    int named = 1 + dice.nextInt(3);
                    for (int at = 0; at < named; at++) {
                        weights.put(atoms.get(dice.nextInt(atoms.size())), dice.nextInt(5) - 2);
                    }
                    weights.values().removeIf(weight -> weight == 0);
                    if (weights.isEmpty()) {
                        continue;
                    }
                    domain = domain.assume(form(weights, dice.nextInt(13) - 6),
                            dice.nextBoolean() ? Rel.LE : Rel.GE, spaces());
                }
            }
            if (domain.isBottom()) {
                continue;
            }
            Map<String, Integer> goal = new LinkedHashMap<>();
            goal.put(LEFT.get(dice.nextInt(3)), 1 + dice.nextInt(2));
            goal.put(RIGHT.get(dice.nextInt(3)), dice.nextBoolean() ? 1 : -1);
            Bounds bounds = domain.boundsOf(form(goal, 0));
            if (bounds.max() == null) {
                continue;
            }
            asked++;
            BigDecimal highest = ((Count) bounds.max().at()).at();
            long reported = highest.setScale(0, RoundingMode.FLOOR).longValueExact();
            long proven = Long.MAX_VALUE;
            for (long bound = reported - 12; bound <= reported + 1; bound++) {
                if (domain.entails(form(goal, -bound), Rel.LE)) {
                    proven = bound;
                    break;
                }
            }
            assertEquals(reported, proven, "a form " + goal + " is reported to come to " + reported
                    + " and is proven to come to " + proven);
        }
        assertTrue(asked > 100, "too few forms were asked for this to hold anything: " + asked);
    }
}
