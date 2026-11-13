package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.RulesAsWritten.Written;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a half-space's rests are asked together comes to what each of them is asked alone.
 *
 * <p>{@link FormReach#rests} works out, for every position of a half-space, the least its rest
 * comes to, and shares between the positions what a premise leaves of all of them. That is a way of
 * asking and not a reading of its own, so every answer is held to {@link FormReach#leastOfTheRestOf}
 * asked of the rest by itself: the same cut, at the same value and as strict.
 *
 * <p>Drawn over five positions with ends of every kind — both, one, none, reached and not — and
 * with now and then a coefficient and a bound far enough apart in scale that the exact arithmetic
 * cannot sum them, which is where the shared sum has to leave the answer to the one that asks
 * alone. The seeds are fixed, so a round that fails is the same round when it is run again.
 */
class TheRestsOfAHalfSpaceAreEachWhatTheRestAskedAloneIsTest {

    private static final List<String> POSITIONS = List.of("a", "b", "cc", "d", "e");

    private static final int CASES = 400;

    /** The sums of the drawn systems hold nothing near the greatest {@code Int}, so one more case is
     *  the chain a path of names makes, which is what the sharing is for. */
    private static final long INT_GREATEST = Long.MAX_VALUE;

    @Test
    void everyRestOfADrawnSystemIsWhatItIsAskedAlone() {
        Random dice = new Random(3167);
        int answered = 0;
        int bounded = 0;
        for (int round = 0; round < CASES; round++) {
            CanonicalOrder<String> order = RulesNamingNoPositionInCommonCloseApartTest.ORDERS
                    .get(round % RulesNamingNoPositionInCommonCloseApartTest.ORDERS.size());
            List<AffineConstraint<String>> rules = RulesAsWritten.statedOnly(someRules(dice),
                    RulesNamingNoPositionInCommonCloseApartTest::spacing);
            if (DifferenceBounds.over(rules, order).holdsNothing()) {
                continue;
            }
            int[] counted = everyRestIsAskedBothWays(rules, someEnds(dice), order);
            answered += counted[0];
            bounded += counted[1];
        }
        assertTrue(answered > 1000, "too few rests were asked for this to hold anything: "
                + answered);
        assertTrue(bounded > 100, "too few rests were bounded for this to hold anything: "
                + bounded);
    }

    /** {@code x_k = p_1 + … + p_k} for each k, each held to the greatest and the least {@code Int}:
     *  the system a chain of names over products leaves, with every one of its forms naming the
     *  positions of the ones before it. */
    @Test
    void everyRestOfAChainOfSumsIsWhatItIsAskedAlone() {
        List<AffineConstraint<String>> rules = new ArrayList<>();
        Map<String, ExactCut> least = new LinkedHashMap<>();
        Map<String, ExactCut> most = new LinkedHashMap<>();
        Map<String, ExactRatio> sum = new LinkedHashMap<>();
        for (int k = 1; k <= 8; k++) {
            String position = "p" + k;
            least.put(position, ExactCut.inclusive(ExactRatio.of(Long.MIN_VALUE)));
            most.put(position, ExactCut.inclusive(ExactRatio.of(INT_GREATEST)));
            sum.put(position, ExactRatio.ONE);
            rules.addAll(RulesAsWritten.statedOnly(List.of(
                    new Written(new LinkedHashMap<>(sum), ExactRatio.of(INT_GREATEST).negated(),
                            Rel.LE),
                    new Written(new LinkedHashMap<>(sum), ExactRatio.of(Long.MIN_VALUE).negated(),
                            Rel.GE)),
                    RulesNamingNoPositionInCommonCloseApartTest::spacing));
        }
        CanonicalOrder<String> order = CanonicalOrder.asTheyAreSpelled();

        int[] counted = everyRestIsAskedBothWays(rules, new Box<>(least, most), order);

        assertTrue(counted[1] > 20, "the chain's rests were not bounded: " + counted[1]);
    }

    /**
     * A premise that leaves the difference of two positions, which the closed differences hold lower
     * than the ends do: no position has an end, so the ends bound nothing and the differences are
     * the only route. {@code a + b + cc <= 0} asked for the rest of {@code a} is {@code b + cc}, and
     * {@code -b - e <= 7} is no difference, so the closed differences do not hold it, but taken off
     * the negated rest it leaves {@code e - cc}, which {@code e - cc <= 2} holds.
     */
    @Test
    void aRestLeftAsADifferenceIsBoundedByTheClosedDifferences() {
        List<AffineConstraint<String>> rules = RulesAsWritten.statedOnly(List.of(
                RulesAsWritten.rule("a + b + cc <= 0"),
                RulesAsWritten.rule("-b - e <= 7"),
                RulesAsWritten.rule("e - cc <= 2")),
                RulesNamingNoPositionInCommonCloseApartTest::spacing);
        CanonicalOrder<String> order = CanonicalOrder.asTheyAreSpelled();

        int[] counted = everyRestIsAskedBothWays(rules, Box.unbounded(), order);

        assertTrue(counted[1] > 0, "no rest was bounded, so the differences were not what asked");
    }

    /**
     * The same for the whole form of a rule, asked for both its ends: {@code b + cc <= 0} has no end
     * of its own to read, and {@code -b - e <= 7} taken off its negation leaves {@code e - cc},
     * which {@code e - cc <= 2} holds — so the form is at least minus nine, by the differences alone.
     */
    @Test
    void aWholeFormLeftAsADifferenceIsBoundedByTheClosedDifferences() {
        List<AffineConstraint<String>> rules = RulesAsWritten.statedOnly(List.of(
                RulesAsWritten.rule("b + cc <= 0"),
                RulesAsWritten.rule("-b - e <= 7"),
                RulesAsWritten.rule("e - cc <= 2")),
                RulesNamingNoPositionInCommonCloseApartTest::spacing);
        CanonicalOrder<String> order = CanonicalOrder.asTheyAreSpelled();

        everyRestIsAskedBothWays(rules, Box.unbounded(), order);

        FormReach<String> reading = FormReach.over(rules, Box.unbounded(),
                DifferenceBounds.over(rules, order), order);
        assertTrue(reading.of(rules.getFirst().form().coefs(), ExactRatio.ZERO).least() != null,
                "the form was not bounded below, so the differences were not what asked");
    }

    /** How many rests were asked and how many of them came to a bound, each held to being asked
     *  alone — by a reading that keeps what every premise leaves and by one that does not. */
    private static int[] everyRestIsAskedBothWays(List<AffineConstraint<String>> rules,
                                                  Box<String> ends,
                                                  CanonicalOrder<String> order) {
        DifferenceBounds<String> differences = DifferenceBounds.over(rules, order);
        FormReach<String> reading = FormReach.over(rules, ends, differences, order);
        FormReach<String> keeping = FormReach.over(rules, ends, differences, order)
                .working(List.of(), new RoundWork<>(rules, ends));
        int asked = 0;
        int bounded = 0;
        for (AffineConstraint<String> rule : rules) {
            Map<String, ExactRatio> whole = rule.form().coefs();
            assertEquals(reading.of(whole, ExactRatio.ZERO), keeping.ofKept(rule, whole),
                    "the form of " + rule + " under " + rules + ", every premise kept");
            for (AffineConstraint.HalfSpace<String> half : rule.halfSpaces()) {
                FormReach<String>.Rests rests = reading.rests(rule, half);
                FormReach<String>.Rests kept = keeping.rests(rule, half);
                for (String atom : half.form().atomsIn(order)) {
                    Map<String, ExactRatio> rest = new LinkedHashMap<>(half.form().coefs());
                    rest.remove(atom);
                    ExactCut alone = reading.leastOfTheRestOf(rule, rest, ExactRatio.ZERO);
                    assertEquals(alone, rests.leastOfTheRest(atom),
                            "the rest of " + atom + " in " + half + " under " + rules);
                    assertEquals(alone, kept.leastOfTheRest(atom),
                            "the rest of " + atom + " in " + half + " under " + rules
                                    + ", every premise kept");
                    asked++;
                    if (alone != null) {
                        bounded++;
                    }
                }
            }
        }
        return new int[] {asked, bounded};
    }

    /** A handful of rules over the positions: bounds, differences and sums weighted unevenly, with
     *  now and then a bound a hair from the others in scale. */
    private static List<Written> someRules(Random dice) {
        List<Written> out = new ArrayList<>();
        int howMany = 2 + dice.nextInt(5);
        for (int i = 0; i < howMany; i++) {
            Map<String, ExactRatio> coefs = new LinkedHashMap<>();
            for (String position : POSITIONS) {
                int weight = dice.nextInt(7) - 3;
                if (weight != 0 && dice.nextInt(3) != 0) {
                    coefs.put(position, ExactRatio.of(weight));
                }
            }
            if (coefs.isEmpty()) {
                continue;
            }
            ExactRatio constant = dice.nextInt(8) == 0 ? RulesNamingNoPositionInCommonCloseApartTest.A_HAIR
                    : ExactRatio.of(dice.nextInt(21) - 10);
            Rel[] all = Rel.values();
            out.add(new Written(coefs, constant, all[dice.nextInt(all.length)]));
        }
        return out;
    }

    /** Ends for some of the positions: at either side or both, reached or not. */
    private static Box<String> someEnds(Random dice) {
        Map<String, ExactCut> least = new LinkedHashMap<>();
        Map<String, ExactCut> most = new LinkedHashMap<>();
        for (String position : POSITIONS) {
            int low = dice.nextInt(15) - 10;
            int high = low + dice.nextInt(12);
            if (dice.nextInt(3) != 0) {
                least.put(position, dice.nextBoolean() || low == high
                        ? ExactCut.inclusive(ExactRatio.of(low))
                        : ExactCut.exclusive(ExactRatio.of(low)));
            }
            if (dice.nextInt(3) != 0) {
                most.put(position, dice.nextBoolean() || low == high
                        ? ExactCut.inclusive(ExactRatio.of(high))
                        : ExactCut.exclusive(ExactRatio.of(high)));
            }
        }
        return new Box<>(least, most);
    }
}
