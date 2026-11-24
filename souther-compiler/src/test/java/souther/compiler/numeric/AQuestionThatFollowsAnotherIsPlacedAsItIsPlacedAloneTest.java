package souther.compiler.numeric;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import org.junit.jupiter.api.Test;
import souther.compiler.numeric.RulesAsWritten.Written;

/**
 * A question made from the question before it, with only the positions it adds compared, puts every
 * position where the question made from all its rules does — for an order that tells every two
 * positions apart, one that puts some of them in one place, and one that runs the other way.
 */
class AQuestionThatFollowsAnotherIsPlacedAsItIsPlacedAloneTest {

    private static final List<String> POSITIONS =
            List.of("a", "b", "bb", "c", "cc", "d", "dd", "e", "f", "ff", "g", "h");

    /** Two positions that start with one letter are one place. */
    private static final CanonicalOrder<String> BY_FIRST_LETTER =
            (one, other) -> Character.compare(one.charAt(0), other.charAt(0));

    private static final List<CanonicalOrder<String>> ORDERS = List.of(
            CanonicalOrder.asTheyAreSpelled(), BY_FIRST_LETTER, (one, other) -> other.compareTo(one));

    private static Granularity spacing(String position) {
        return Granularity.DISCRETE;
    }

    private static Map<String, Integer> placesAlone(List<AffineConstraint<String>> rules,
                                                    CanonicalOrder<String> order) {
        return ClosureQuestion.of(rules, AQuestionThatFollowsAnotherIsPlacedAsItIsPlacedAloneTest::spacing,
                order).places();
    }

    @Test
    void everyPositionIsWhereItIsPlacedAloneWhateverIsAddedAfterWhatOrder() {
        Random dice = new Random(316704);
        int followed = 0;
        long placedFromBefore = ClosureQuestion.placedFromBefore();
        for (int sequence = 0; sequence < 300; sequence++) {
            CanonicalOrder<String> order = ORDERS.get(sequence % ORDERS.size());
            List<AffineConstraint<String>> rules = new ArrayList<>();
            ClosureQuestion<String> before = null;
            for (int step = 0; step < 8; step++) {
                int howMany = 1 + dice.nextInt(3);
                for (int each = 0; each < howMany; each++) {
                    Map<String, ExactRatio> coefs = new LinkedHashMap<>();
                    int named = 1 + dice.nextInt(3);
                    for (int at = 0; at < named; at++) {
                        coefs.put(POSITIONS.get(dice.nextInt(POSITIONS.size())),
                                ExactRatio.of(1 + dice.nextInt(3)));
                    }
                    List<AffineConstraint<String>> read = RulesAsWritten.statedOnly(
                            List.of(new Written(coefs, ExactRatio.of(dice.nextInt(9) - 4), Rel.LE)),
                            AQuestionThatFollowsAnotherIsPlacedAsItIsPlacedAloneTest::spacing);
                    rules.addAll(read);
                }
                ClosureQuestion<String> alone = ClosureQuestion.of(rules,
                        AQuestionThatFollowsAnotherIsPlacedAsItIsPlacedAloneTest::spacing, order);
                ClosureQuestion<String> following = ClosureQuestion.following(before, rules,
                        AQuestionThatFollowsAnotherIsPlacedAsItIsPlacedAloneTest::spacing, order,
                        weighed -> ClosureQuestion.placesIn(weighed, order));
                assertEquals(placesAlone(rules, order), following.places(), "after " + rules);
                assertEquals(alone, following, "after " + rules);
                if (before != null && rules.size() > before.rules().size()) {
                    followed++;
                }
                before = following;
            }
        }
        assertTrue(followed > 500, "too few questions followed another: " + followed);
        assertEquals(followed, ClosureQuestion.placedFromBefore() - placedFromBefore,
                "every question that followed another, by an order it was placed by, was placed from it");
    }
}
