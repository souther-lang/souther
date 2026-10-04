package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.AffineConstraint.Read;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a closure worked out from a question comes to is what the rules come to when they are
 * closed as they were handed over.
 *
 * <p>Two roads to one closure. A closure that is kept is worked out from its question, reading the
 * spacing and the order back off it, so that it is settled by what it is kept under; one that is not
 * kept is worked out from the rules, the spacing and the order it was handed. They have to be the
 * same closure, or a reader would be answered one way where closures are kept and another where they
 * are not.
 *
 * <p>Asked over rules drawn at random, under an order that ties two positions as well as orders
 * that tie none, and with positions spaced both ways. Where a rule weighs the two tied positions
 * together, both roads refuse it.
 */
class AClosureOfAQuestionIsTheClosureOfItsRulesTest {

    private static final List<String> POSITIONS = List.of("a", "b", "cc");
    private static final int CASES = 400;

    @Test
    void bothRoadsCloseTheRulesAlike() {
        Function<String, Granularity> spacing =
                atom -> atom.equals("b") ? Granularity.DENSE : Granularity.DISCRETE;
        List<CanonicalOrder<String>> orders = List.of(
                String::compareTo,
                (one, other) -> other.compareTo(one),
                (one, other) -> Integer.compare(one.length(), other.length()));
        Random dice = new Random(2126);
        int closed = 0;
        int refused = 0;
        for (int round = 0; round < CASES; round++) {
            List<AffineConstraint<String>> rules = someRules(dice, spacing);
            CanonicalOrder<String> order = orders.get(round % orders.size());

            Outcome asHanded = outcome(() -> ClosedState.of(rules, spacing, order));
            Outcome asAsked = outcome(() ->
                    ClosedState.of(ClosureQuestion.of(rules, spacing, order)));

            assertEquals(asHanded, asAsked, () -> "the two roads closed " + rules + " apart");
            if (asHanded.refused()) {
                refused++;
            } else if (!asHanded.holdsNothing()) {
                closed++;
            }
        }
        assertTrue(closed > 0 && refused > 0,
                "closed " + closed + " and refused " + refused + ", so this compared little");
    }

    /** What one road came to, as a value two roads can be compared by. */
    private record Outcome(boolean refused, boolean holdsNothing, Object box,
                           boolean everyBoundWasComposed) {}

    private interface Closing {
        ClosedState<String> close();
    }

    private static Outcome outcome(Closing closing) {
        ClosedState<String> closed;
        try {
            closed = closing.close();
        } catch (IllegalStateException refusal) {
            return new Outcome(true, false, refusal.getMessage(), false);
        }
        return new Outcome(false, closed.holdsNothing(),
                closed.holdsNothing() ? null : closed.box(), closed.everyBoundWasComposed());
    }

    private static List<AffineConstraint<String>> someRules(Random dice,
                                                            Function<String, Granularity> spacing) {
        List<AffineConstraint<String>> out = new ArrayList<>();
        int howMany = 1 + dice.nextInt(4);
        for (int i = 0; i < howMany; i++) {
            Map<String, ExactRatio> coefs = new LinkedHashMap<>();
            for (String position : POSITIONS) {
                int weight = dice.nextInt(5) - 2;
                if (weight != 0) {
                    coefs.put(position, ExactRatio.of(weight));
                }
            }
            if (coefs.isEmpty()) {
                continue;
            }
            Rel[] all = Rel.values();
            if (AffineConstraint.of(coefs, ExactRatio.of(dice.nextInt(15) - 7),
                    all[dice.nextInt(all.length)], spacing) instanceof Read.Stated<String> it) {
                out.add(it.constraint());
            }
        }
        return out;
    }
}
