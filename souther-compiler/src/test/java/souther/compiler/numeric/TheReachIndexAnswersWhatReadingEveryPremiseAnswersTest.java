package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a form runs between, read from the index of the premises over two positions, is what it runs
 * between read from every premise.
 *
 * <p>The index is a way of finding the lowest of what the premises leave a form and not a second
 * account of what one leaves, so it is held to the reading that has no index
 * ({@link FormReach#of}) over rules drawn at random: weights of every sign and none, relations that
 * reach their value and ones that do not, equalities, and ends that are missing on one side or both.
 * Both ends of a form are compared, and the value and whether it is reached.
 */
class TheReachIndexAnswersWhatReadingEveryPremiseAnswersTest {

    private static final CanonicalOrder<String> ORDER = CanonicalOrder.asTheyAreSpelled();

    private static final String[] RELATIONS = {"<=", "<", ">=", ">", "="};

    private static RulesAsWritten.Written drawn(Random random) {
        int a = random.nextInt(9) - 4;
        int b = random.nextInt(9) - 4;
        if (a == 0 && b == 0) {
            a = 1;
        }
        List<String> terms = new ArrayList<>();
        if (a != 0) {
            terms.add(a + "a");
        }
        if (b != 0) {
            terms.add(b + "b");
        }
        return RulesAsWritten.rule(String.join(" + ", terms) + " " + RELATIONS[random.nextInt(5)]
                + " " + (random.nextInt(25) - 12));
    }

    private static Box<String> endsDrawn(Random random) {
        Map<String, ExactCut> atLeast = new LinkedHashMap<>();
        Map<String, ExactCut> atMost = new LinkedHashMap<>();
        for (String position : List.of("a", "b")) {
            if (random.nextInt(10) < 7) {
                atLeast.put(position, new ExactCut(ExactRatio.of(random.nextInt(41) - 30),
                        random.nextBoolean()));
            }
            if (random.nextInt(10) < 7) {
                atMost.put(position, new ExactCut(ExactRatio.of(random.nextInt(41) - 10),
                        random.nextBoolean()));
            }
        }
        return new Box<>(atLeast, atMost);
    }

    private static boolean same(ExactCut one, ExactCut other) {
        return one == null ? other == null : other != null
                && one.at().compareTo(other.at()) == 0 && one.inclusive() == other.inclusive();
    }

    @Test
    void everyFormOfDrawnRulesRunsBetweenTheSameEndsEitherWay() {
        Random random = new Random(7);
        int compared = 0;
        int indexed = 0;
        for (int each = 0; each < 3000; each++) {
            List<RulesAsWritten.Written> written = new ArrayList<>();
            int count = 10 + random.nextInt(25);
            for (int rule = 0; rule < count; rule++) {
                written.add(drawn(random));
            }
            List<AffineConstraint<String>> rules = RulesAsWritten.statedOnly(written,
                    RulesNamingNoPositionInCommonCloseApartTest::spacing);
            DifferenceBounds<String> differences = DifferenceBounds.over(rules, ORDER);
            if (differences.holdsNothing()) {
                continue;
            }
            FormReach<String> reading = FormReach.over(rules, endsDrawn(random), differences, ORDER);
            FormReach.Indexed<String> index = reading.indexedPremises();
            if (index == null) {
                continue;
            }
            indexed++;
            Set<Map<String, ExactRatio>> forms = new LinkedHashSet<>();
            for (AffineConstraint<String> rule : rules) {
                forms.add(rule.form().coefs());
            }
            for (int form = 0; form < 20; form++) {
                int a = random.nextInt(9) - 4;
                int b = random.nextInt(9) - 4;
                if (a != 0 && b != 0) {
                    Map<String, ExactRatio> drawn = new LinkedHashMap<>();
                    drawn.put("a", ExactRatio.of(a));
                    drawn.put("b", ExactRatio.of(b));
                    forms.add(drawn);
                }
            }
            for (Map<String, ExactRatio> form : forms) {
                if (form.size() < 2) {
                    continue;
                }
                Reach quick = reading.reachWith(index, form);
                assertTrue(quick != null, "a form of two positions over two positions is read "
                        + "from the index here: " + form);
                Reach slow = reading.of(form, ExactRatio.ZERO);
                compared++;
                assertTrue(same(slow.most(), quick.most()) && same(slow.least(), quick.least()),
                        "the form " + form + " runs between " + slow + " where it is read from "
                                + "every premise and between " + quick + " from the index, over "
                                + rules + " in " + reading.ends());
            }
        }
        assertTrue(indexed > 300, "only " + indexed + " of the drawn rules were indexed, which is "
                + "too few to say the index was asked");
        assertTrue(compared > 5000, "only " + compared + " forms were compared");
    }

    @Test
    void aReadingOverAnythingButTwoPositionsOrFewPremisesIsNotIndexed() {
        List<AffineConstraint<String>> three = RulesAsWritten.statedOnly(RulesAsWritten.rules(
                "a + b + c <= 3", "a - b <= 1", "b - c <= 2", "c - a <= 4", "a + c <= 9",
                "2a - c <= 5", "a + 2b <= 6", "b + 2c <= 7", "3a + b <= 8", "a + 3c <= 8",
                "a + b <= 5", "b + c <= 5", "a + c <= 5", "2a + b <= 5", "2b + c <= 5",
                "2a + c <= 5", "a <= 4"), RulesNamingNoPositionInCommonCloseApartTest::spacing);
        FormReach<String> wide = FormReach.over(three, Box.unbounded(),
                DifferenceBounds.over(three, ORDER), ORDER);
        assertEquals(null, wide.indexedPremises(), "three positions are not indexed");
        List<AffineConstraint<String>> few = RulesAsWritten.statedOnly(
                RulesAsWritten.rules("a + b <= 3", "a - b <= 1"),
                RulesNamingNoPositionInCommonCloseApartTest::spacing);
        FormReach<String> narrow = FormReach.over(few, Box.unbounded(),
                DifferenceBounds.over(few, ORDER), ORDER);
        assertEquals(null, narrow.indexedPremises(),
                "a few premises are read one by one, as making the index costs more than they do");
    }
}
