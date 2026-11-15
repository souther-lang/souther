package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A closure that asks whether the rules leave a form nothing at the start of one round and of the
 * last, and not of every round, is the closure that asks every round.
 *
 * <p>Every round's ends are inside the round before's, so a form left nothing by an earlier round's
 * ends is left nothing by the last round's. Held to the closure that asks every round
 * ({@link ClosedState#closedAskingEveryRound}) over rules drawn at random: what they leave, whether
 * the rounds ran out, and whether every bound was composed. The rules are over two positions and
 * over three, with holes among them now and then, and with and without bounds on each position, so
 * that some leave nothing, some settle in a round and some take several.
 */
class AClosureAskedOfFewerRoundsIsTheClosureAskedOfEveryRoundTest {

    private static final CanonicalOrder<String> ORDER = CanonicalOrder.asTheyAreSpelled();

    private static final String[] RELATIONS = {"<=", "<", ">=", ">", "=", "<=", ">=", "<="};

    private static String drawn(Random random, int positions, boolean holes) {
        List<String> terms = new ArrayList<>();
        for (int at = 0; at < positions; at++) {
            int weight = random.nextInt(7) - 3;
            if (weight != 0 && (terms.isEmpty() || random.nextInt(3) > 0)) {
                terms.add(weight + "" + "abc".charAt(at));
            }
        }
        if (terms.isEmpty()) {
            terms.add("1a");
        }
        String relation = holes && random.nextInt(8) == 0 ? "/=" : RELATIONS[random.nextInt(8)];
        return String.join(" + ", terms) + " " + relation + " " + (random.nextInt(21) - 10);
    }

    /**
     * The rules a chain of sums over two inputs comes to, each partial sum held in the range of a
     * type: {@code a_i = x·u_i + j·v_i} between {@code -limit} and {@code limit - 1}, with the
     * weights of a chain that adds the one before to itself or only to {@code j}, and then a few
     * more that cut a region out of it, which is where what is left takes several rounds to say.
     */
    private static List<RulesAsWritten.Written> aChain(Random random) {
        boolean doubling = random.nextBoolean();
        long limit = 1L << (5 + random.nextInt(6));
        int links = 3 + random.nextInt(10);
        List<RulesAsWritten.Written> written = new ArrayList<>();
        long x = 1;
        long j = 0;
        for (int link = 1; link <= links; link++) {
            x = doubling ? 2 * x : x;
            j = doubling ? 2 * j + 1 : j + 1;
            String sum = x + "a + " + j + "b";
            written.add(RulesAsWritten.rule(sum + " <= " + (limit - 1)));
            written.add(RulesAsWritten.rule(sum + " >= " + -limit));
        }
        written.add(RulesAsWritten.rule("1a <= " + (limit - 1)));
        written.add(RulesAsWritten.rule("1a >= " + -limit));
        written.add(RulesAsWritten.rule("1b <= " + (limit - 1)));
        written.add(RulesAsWritten.rule("1b >= " + -limit));
        for (int extra = random.nextInt(4); extra > 0; extra--) {
            long at = 1L + random.nextInt(links);
            long weight = doubling ? 1L << at : 1;
            String sum = weight + "a + " + (doubling ? weight - 1 : at) + "b";
            long bound = random.nextInt((int) (2 * limit)) - limit;
            written.add(RulesAsWritten.rule(sum + (random.nextBoolean() ? " >= " : " <= ") + bound));
        }
        return written;
    }

    /**
     * Two rules that cross only through an end that three rounds of narrowing bring: {@code b} is
     * at least twice {@code c}, which is at least twice {@code d}, which is at least twice
     * {@code e}, which is at least three, so {@code b} is at least 24 only at the start of the
     * round after the third. With that end, {@code a + b} is at most {@code 10 - 24} by the first
     * rule and at least one by the second, which no earlier round's ends say.
     */
    private static List<RulesAsWritten.Written> aCrossingThatNeedsThreeRounds(int bound) {
        return RulesAsWritten.rules("1a + 2b <= " + bound, "1a + 1b >= 1", "1e >= 3",
                "1d - 2e >= 0", "1c - 2d >= 0", "1b - 2c >= 0");
    }

    /** A number of a scale a sum of it and a small one may have no representation at. */
    private static ExactRatio ofAScale(Random random) {
        int whole = random.nextInt(11) - 5;
        int[] scales = {0, 0, 0, 0, 1, 6, 60, 600, 6000};
        ExactRatio scaled = ExactRatio.of(whole).times(
                ExactRatio.tenTo(scales[random.nextInt(scales.length)])).orNull();
        return scaled == null ? ExactRatio.of(whole) : scaled;
    }

    @Test
    void rulesOfEveryScaleLeaveWhatEveryRoundAskedLeaves() {
        Random random = new Random(5);
        int empty = 0;
        int settled = 0;
        for (int each = 0; each < 1500; each++) {
            int positions = 2 + random.nextInt(2);
            List<RulesAsWritten.Written> written = new ArrayList<>();
            int count = 3 + random.nextInt(10);
            for (int rule = 0; rule < count; rule++) {
                Map<String, ExactRatio> coefs = new LinkedHashMap<>();
                for (int at = 0; at < positions; at++) {
                    int weight = random.nextInt(7) - 3;
                    if (weight != 0 && (coefs.isEmpty() || random.nextInt(3) > 0)) {
                        coefs.put("abc".substring(at, at + 1), ExactRatio.of(weight));
                    }
                }
                if (coefs.isEmpty()) {
                    coefs.put("a", ExactRatio.ONE);
                }
                written.add(new RulesAsWritten.Written(coefs, ofAScale(random),
                        RULE_RELATIONS[random.nextInt(RULE_RELATIONS.length)]));
            }
            List<AffineConstraint<String>> rules = RulesAsWritten.statedOnly(written,
                    RulesNamingNoPositionInCommonCloseApartTest::spacing);
            ClosedState<String> reference = ClosedState.closedAskingEveryRound(rules,
                    RulesNamingNoPositionInCommonCloseApartTest::spacing, ORDER);
            ClosedState<String> closed = ClosedState.closedTogether(rules,
                    RulesNamingNoPositionInCommonCloseApartTest::spacing, ORDER);
            assertEquals(reference.holdsNothing(), closed.holdsNothing(),
                    "whether the rules leave nothing, of " + written);
            if (closed.holdsNothing()) {
                empty++;
                continue;
            }
            assertEquals(reference.box(), closed.box(), "what the rules leave, of " + written);
            settled++;
        }
        assertTrue(empty > 100 && settled > 100, "the rules left nothing " + empty
                + " times and something " + settled + " times");
    }

    private static final Rel[] RULE_RELATIONS = {Rel.LE, Rel.LT, Rel.GE, Rel.GT, Rel.EQ, Rel.LE,
            Rel.GE};

    /**
     * The reading of a form is a partial function: a sum of two numbers whose exponents are far
     * apart has no representation. Nought added to a number of that size is held and one taken from
     * it is not, so what a form leaves is found at the ends a position has and lost at ends inside
     * them. That is what the closure asks every round for.
     */
    @Test
    void aSumOfNumbersFarApartInScaleIsNotHeldWhereTheSumWithNoughtIs() {
        ExactRatio huge = ExactRatio.tenTo(3_000_000_000L);
        assertTrue(huge.plus(ExactRatio.ZERO).orNull() != null, "nought is added to it");
        assertEquals(null, huge.plus(ExactRatio.of(-1)).orNull(), "one is not taken from it");
    }

    @Test
    void everyRoundIsAskedWhereARuleHasAHoleOrANumberTooWideToBeSureOf() {
        assertEquals(false, ClosedState.mustAskEveryRound(RulesAsWritten.statedOnly(
                RulesAsWritten.rules("1a + 2b <= 10", "1a >= 3"),
                RulesNamingNoPositionInCommonCloseApartTest::spacing)), "rules of small numbers");
        assertEquals(true, ClosedState.mustAskEveryRound(RulesAsWritten.statedOnly(
                RulesAsWritten.rules("1a + 2b <= 10", "1a /= 3"),
                RulesNamingNoPositionInCommonCloseApartTest::spacing)), "a hole");
        Map<String, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put("a", ExactRatio.of(2));
        coefs.put("b", ExactRatio.ONE);
        for (long scale : new long[] {ExactRatio.MODEST + 1, 3_000_000_000L}) {
            assertEquals(true, ClosedState.mustAskEveryRound(RulesAsWritten.statedOnly(
                    List.of(new RulesAsWritten.Written(coefs,
                            ExactRatio.tenTo(scale).negated(), Rel.LE)),
                    RulesNamingNoPositionInCommonCloseApartTest::spacing)),
                    "a bound of a scale of " + scale);
        }
        assertEquals(false, ClosedState.mustAskEveryRound(RulesAsWritten.statedOnly(
                List.of(new RulesAsWritten.Written(coefs,
                        ExactRatio.tenTo(ExactRatio.MODEST).negated(), Rel.LE)),
                RulesNamingNoPositionInCommonCloseApartTest::spacing)),
                "a bound of the widest scale there is no doubt of");
    }

    @Test
    void aCrossingOnlyTheLastRoundSeesIsFoundByTheClosureAskedOfFewer() {
        for (int bound : new int[] {10, -30, 100}) {
            List<AffineConstraint<String>> rules = RulesAsWritten.statedOnly(
                    aCrossingThatNeedsThreeRounds(bound),
                    RulesNamingNoPositionInCommonCloseApartTest::spacing);
            ClosedState<String> reference = ClosedState.closedAskingEveryRound(rules,
                    RulesNamingNoPositionInCommonCloseApartTest::spacing, ORDER);
            ClosedState<String> closed = ClosedState.closedTogether(rules,
                    RulesNamingNoPositionInCommonCloseApartTest::spacing, ORDER);
            assertEquals(reference.holdsNothing(), closed.holdsNothing(),
                    "whether a + 2b <= " + bound + " leaves nothing");
            if (bound == 10) {
                assertTrue(closed.holdsNothing(),
                        "a + 2b <= 10 and a + b >= 1 cross once b is at least 24");
            }
        }
    }

    @Test
    void aChainOfSumsLeavesWhatEveryRoundAskedLeaves() {
        Random random = new Random(7);
        int empty = 0;
        int settled = 0;
        for (int each = 0; each < 400; each++) {
            List<AffineConstraint<String>> rules = RulesAsWritten.statedOnly(aChain(random),
                    RulesNamingNoPositionInCommonCloseApartTest::spacing);
            ClosedState<String> reference = ClosedState.closedAskingEveryRound(rules,
                    RulesNamingNoPositionInCommonCloseApartTest::spacing, ORDER);
            ClosedState<String> closed = ClosedState.closedTogether(rules,
                    RulesNamingNoPositionInCommonCloseApartTest::spacing, ORDER);
            assertEquals(reference.holdsNothing(), closed.holdsNothing(),
                    "whether the rules leave nothing, of " + rules);
            if (closed.holdsNothing()) {
                empty++;
                continue;
            }
            assertEquals(reference.box(), closed.box(), "what the rules leave, of " + rules);
            assertEquals(reference.status(), closed.status(), "whether the rounds ran out, of " + rules);
            settled++;
        }
        assertTrue(empty > 30 && settled > 30, "the chains left nothing " + empty
                + " times and something " + settled + " times, which is too few of one to say the "
                + "two closures agree about it");
    }

    @Test
    void drawnRulesLeaveWhatEveryRoundAskedLeaves() {
        Random random = new Random(7);
        int empty = 0;
        int settled = 0;
        for (int each = 0; each < 1500; each++) {
            int positions = 2 + random.nextInt(2);
            boolean holes = random.nextInt(4) == 0;
            List<RulesAsWritten.Written> written = new ArrayList<>();
            int count = 3 + random.nextInt(28);
            for (int rule = 0; rule < count; rule++) {
                written.add(RulesAsWritten.rule(drawn(random, positions, holes)));
            }
            if (random.nextBoolean()) {
                written = RulesAsWritten.boxed(written, List.of("a", "b", "c").subList(0, positions),
                        -random.nextInt(40), random.nextInt(40));
            }
            List<AffineConstraint<String>> rules = RulesAsWritten.statedOnly(written,
                    RulesNamingNoPositionInCommonCloseApartTest::spacing);
            ClosedState<String> reference = ClosedState.closedAskingEveryRound(rules,
                    RulesNamingNoPositionInCommonCloseApartTest::spacing, ORDER);
            ClosedState<String> closed = ClosedState.closedTogether(rules,
                    RulesNamingNoPositionInCommonCloseApartTest::spacing, ORDER);
            assertEquals(reference.holdsNothing(), closed.holdsNothing(),
                    "whether the rules leave nothing, of " + rules);
            if (closed.holdsNothing()) {
                empty++;
                continue;
            }
            assertEquals(reference.box(), closed.box(), "what the rules leave, of " + rules);
            assertEquals(reference.status(), closed.status(), "whether the rounds ran out, of " + rules);
            assertEquals(reference.everyBoundWasComposed(), closed.everyBoundWasComposed(),
                    "whether every bound was composed, of " + rules);
            settled++;
        }
        assertTrue(empty > 100 && settled > 100, "the drawn rules left nothing " + empty
                + " times and something " + settled + " times, which is too few of one to say "
                + "the two closures agree about it");
    }
}
