package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;
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
 * What a form runs between, and what is left of the rest of a rule, read from the tree of the
 * premises, is what they are read from every premise.
 *
 * <p>The tree chooses which premises are read and says nothing of what one leaves a form, so it is
 * held to the reading that has no tree ({@link FormReach#readingEveryPremise}) over rules drawn at
 * random: two to four positions, weights of every sign and none, whole and not, relations that reach
 * their value and ones that do not, equalities, rules that are the difference of two positions so
 * that the closed differences bound something lower than the ends do, and ends that are missing on
 * one side or both. Both ends of a form are compared, and the value and whether it is reached.
 */
class ThePremiseTreeAnswersWhatReadingEveryPremiseAnswersTest {

    private static final CanonicalOrder<String> ORDER = CanonicalOrder.asTheyAreSpelled();

    private static final String[] POSITIONS = {"a", "b", "c", "d"};

    private static final Rel[] RELATIONS = {Rel.LE, Rel.LT, Rel.GE, Rel.GT, Rel.EQ, Rel.LE, Rel.GE};

    private static ExactRatio weight(Random random, int whole) {
        return switch (random.nextInt(8)) {
            case 0 -> ExactRatio.of(whole).dividedBy(ExactRatio.of(2)).orNull();
            case 1 -> ExactRatio.of(whole).dividedBy(ExactRatio.of(10)).orNull();
            default -> ExactRatio.of(whole);
        };
    }

    private static RulesAsWritten.Written drawn(Random random, int positions) {
        Map<String, ExactRatio> coefs = new LinkedHashMap<>();
        if (random.nextInt(4) == 0) {
            int one = random.nextInt(positions);
            int other = (one + 1 + random.nextInt(positions - 1)) % positions;
            ExactRatio by = ExactRatio.of(1 + random.nextInt(3));
            coefs.put(POSITIONS[one], by);
            coefs.put(POSITIONS[other], by.negated());
        } else {
            for (int at = 0; at < positions; at++) {
                int whole = random.nextInt(9) - 4;
                if (whole != 0 && (coefs.isEmpty() || random.nextInt(3) > 0)) {
                    coefs.put(POSITIONS[at], weight(random, whole));
                }
            }
            if (coefs.isEmpty()) {
                coefs.put(POSITIONS[0], ExactRatio.ONE);
            }
        }
        return new RulesAsWritten.Written(coefs, scaled(random, random.nextInt(25) - 12),
                RELATIONS[random.nextInt(RELATIONS.length)]);
    }

    /** {@code whole}, now and then times a power of ten as far from the rest as a double's last
     *  place is from its first. */
    private static ExactRatio scaled(Random random, int whole) {
        return random.nextInt(6) == 0
                ? ExactRatio.of(BigInteger.valueOf(whole).multiply(
                        BigInteger.TEN.pow(5 + random.nextInt(25))))
                : ExactRatio.of(whole);
    }

    private static Box<String> endsDrawn(Random random, int positions) {
        Map<String, ExactCut> atLeast = new LinkedHashMap<>();
        Map<String, ExactCut> atMost = new LinkedHashMap<>();
        for (int at = 0; at < positions; at++) {
            if (random.nextInt(10) < 7) {
                atLeast.put(POSITIONS[at], new ExactCut(scaled(random, random.nextInt(41) - 30),
                        random.nextBoolean()));
            }
            if (random.nextInt(10) < 7) {
                atMost.put(POSITIONS[at], new ExactCut(scaled(random, random.nextInt(41) - 10),
                        random.nextBoolean()));
            }
        }
        return new Box<>(atLeast, atMost);
    }

    private static boolean same(ExactCut one, ExactCut other) {
        return one == null ? other == null : other != null
                && one.at().compareTo(other.at()) == 0 && one.inclusive() == other.inclusive();
    }

    private static List<AffineConstraint<String>> rulesDrawn(Random random, int positions) {
        List<RulesAsWritten.Written> written = new ArrayList<>();
        int count = 10 + random.nextInt(25);
        for (int rule = 0; rule < count; rule++) {
            written.add(drawn(random, positions));
        }
        return RulesAsWritten.statedOnly(written, RulesNamingNoPositionInCommonCloseApartTest::spacing);
    }

    @Test
    void everyFormOfDrawnRulesRunsBetweenTheSameEndsEitherWay() {
        Random random = new Random(7);
        int compared = 0;
        long before = PremiseTree.steps();
        for (int each = 0; each < 3000; each++) {
            int positions = 2 + random.nextInt(3);
            List<AffineConstraint<String>> rules = rulesDrawn(random, positions);
            DifferenceBounds<String> differences = DifferenceBounds.over(rules, ORDER);
            if (differences.holdsNothing()) {
                continue;
            }
            FormReach<String> reading = FormReach.over(rules, endsDrawn(random, positions),
                    differences, ORDER);
            FormReach<String> every = reading.readingEveryPremise();
            Set<Map<String, ExactRatio>> forms = new LinkedHashSet<>();
            for (AffineConstraint<String> rule : rules) {
                forms.add(rule.form().coefs());
            }
            for (int form = 0; form < 20; form++) {
                Map<String, ExactRatio> drawn = new LinkedHashMap<>();
                for (int at = 0; at < positions; at++) {
                    int whole = random.nextInt(9) - 4;
                    if (whole != 0) {
                        drawn.put(POSITIONS[at], weight(random, whole));
                    }
                }
                if (drawn.size() > 1) {
                    forms.add(drawn);
                }
            }
            for (Map<String, ExactRatio> form : forms) {
                if (form.size() < 2) {
                    continue;
                }
                Reach slow = every.of(form, ExactRatio.ZERO);
                Reach quick = reading.of(form, ExactRatio.ZERO);
                compared++;
                assertTrue(same(slow.most(), quick.most()) && same(slow.least(), quick.least()),
                        "the form " + form + " runs between " + slow + " where it is read from "
                                + "every premise and between " + quick + " from the tree, over "
                                + rules + " in " + reading.ends());
            }
        }
        assertTrue(compared > 20000, "only " + compared + " forms were compared");
        assertTrue(PremiseTree.steps() - before > 100000, "the tree was asked too little to say it "
                + "answers as every premise does");
    }

    @Test
    void theRestOfEveryRuleIsLeftWhatEveryPremiseLeavesItEitherWay() {
        Random random = new Random(11);
        int compared = 0;
        for (int each = 0; each < 1500; each++) {
            int positions = 3 + random.nextInt(2);
            List<AffineConstraint<String>> rules = rulesDrawn(random, positions);
            DifferenceBounds<String> differences = DifferenceBounds.over(rules, ORDER);
            if (differences.holdsNothing()) {
                continue;
            }
            FormReach<String> reading = FormReach.over(rules, endsDrawn(random, positions),
                    differences, ORDER);
            FormReach<String> every = reading.readingEveryPremise();
            for (AffineConstraint<String> rule : rules) {
                for (AffineConstraint.HalfSpace<String> half : rule.halfSpaces()) {
                    FormReach<String>.Rests quick = reading.rests(rule, half);
                    FormReach<String>.Rests slow = every.rests(rule, half);
                    for (String atom : half.form().coefs().keySet()) {
                        compared++;
                        assertTrue(same(slow.leastOfTheRest(atom), quick.leastOfTheRest(atom)),
                                "what is left of the rest of " + half + " without " + atom + " is "
                                        + slow.leastOfTheRest(atom) + " from every premise and "
                                        + quick.leastOfTheRest(atom) + " from the tree, over "
                                        + rules + " in " + reading.ends());
                    }
                }
            }
        }
        assertTrue(compared > 20000, "only " + compared + " rests were compared");
    }

    @Test
    void aReadingOfFewPremisesIsNotPutInATree() {
        List<AffineConstraint<String>> few = RulesAsWritten.statedOnly(
                RulesAsWritten.rules("a + b <= 3", "a - b <= 1"),
                RulesNamingNoPositionInCommonCloseApartTest::spacing);
        FormReach<String> reading = FormReach.over(few, Box.unbounded(),
                DifferenceBounds.over(few, ORDER), ORDER);
        long before = PremiseTree.steps();
        Reach reach = reading.of(Map.of("a", ExactRatio.ONE, "b", ExactRatio.of(2)), ExactRatio.ZERO);
        assertEquals(before, PremiseTree.steps(),
                "a few premises are read one by one, as making the tree costs more than they do");
        assertTrue(reach != null);
    }
}
