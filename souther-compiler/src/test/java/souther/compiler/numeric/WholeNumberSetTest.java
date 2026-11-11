package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A set held by its ends and remainders answers membership and the nearest members exactly, and
 * the meet of two is the numbers both hold, whichever way they are written.
 */
class WholeNumberSetTest {

    private static BigInteger n(long value) {
        return BigInteger.valueOf(value);
    }

    private static WholeNumberSet evens() {
        return WholeNumberSet.ofClass(new Congruences(BigInteger.ZERO, n(2)));
    }

    private static WholeNumberSet nonNegative() {
        return WholeNumberSet.ofRuns(WholeNumberRuns.one(BigInteger.ZERO, null));
    }

    @Test
    void theEvenNumbersAreHeldWithoutListingThem() {
        WholeNumberSet evens = evens();
        assertTrue(evens.holds(n(-4)));
        assertFalse(evens.holds(n(3)));
        assertEquals(n(2), evens.greatestAtOrBelow(n(3)));
        assertEquals(n(4), evens.leastAtOrAbove(n(3)));
        assertNull(evens.least());
    }

    @Test
    void theMeetOfEvensAndNonNegativesHasItsEndsAtMembers() {
        WholeNumberSet both = evens().and(nonNegative());
        assertEquals(n(0), both.least());
        assertNull(both.greatest());
        assertNull(both.greatestAtOrBelow(n(-1)));
        assertEquals(n(2), both.greatestAtOrBelow(n(3)));
    }

    /** Evens and odds share no number, and the multiples of two and of three share those of six. */
    @Test
    void twoRemaindersMeetWhereTheirCongruencesDo() {
        WholeNumberSet odds = WholeNumberSet.ofClass(new Congruences(BigInteger.ONE, n(2)));
        assertTrue(evens().and(odds).isNone());
        WholeNumberSet threes = WholeNumberSet.ofClass(new Congruences(BigInteger.ZERO, n(3)));
        WholeNumberSet sixes = evens().and(threes);
        assertTrue(sixes.holds(n(12)));
        assertFalse(sixes.holds(n(9)));
        assertFalse(sixes.holds(n(8)));
    }

    /** Nought and the numbers from six on, which a filter keeping six or more totals. */
    @Test
    void aSetOfRunsHoldsNoughtAndSixAndMoreAndNothingBetween() {
        WholeNumberSet kept = WholeNumberSet.ofRuns(WholeNumberRuns.one(BigInteger.ZERO,
                BigInteger.ZERO).or(WholeNumberRuns.one(n(6), null)));
        for (long between = 1; between <= 5; between++) {
            assertFalse(kept.holds(n(between)), "held " + between);
            assertEquals(n(0), kept.greatestAtOrBelow(n(between)));
            assertEquals(n(6), kept.leastAtOrAbove(n(between)));
        }
        assertTrue(kept.holds(n(6)));
        assertEquals(n(0), kept.least());
        assertNull(kept.greatest());
    }

    /** {@code 2·x - c = 0} for any {@code x}: {@code c} is even. */
    @Test
    void whatTwiceANumberLeavesOfTheOneBesideItIsTheEvens() {
        WholeNumberSet cs = WholeNumberSet.EVERY.valuesBeside(n(2), n(-1), n(0));
        assertTrue(cs.holds(n(4)));
        assertTrue(cs.holds(n(-6)));
        assertFalse(cs.holds(n(3)));
        // With weight one, c = x: every number.
        assertTrue(WholeNumberSet.EVERY.valuesBeside(n(1), n(-1), n(0)).holds(n(3)));
    }

    /** {@code x ≥ 6}, twice: {@code c = 2·x} is the even numbers from twelve. */
    @Test
    void theEndsOfTheRunAreCarriedToTheOtherNumber() {
        WholeNumberSet x = WholeNumberSet.ofRuns(WholeNumberRuns.one(n(6), null));
        WholeNumberSet cs = x.valuesBeside(n(2), n(-1), n(0));
        assertEquals(n(12), cs.least());
        assertNull(cs.greatest());
        assertTrue(cs.holds(n(12)));
        assertFalse(cs.holds(n(10)));
        assertFalse(cs.holds(n(13)));
    }

    /** {@code 3·x + 2·c = 7} has solutions {@code x = 1, c = 2} and nothing for even {@code x}. */
    @Test
    void aWeightedEquationLeavesTheClassItsSolutionsAreIn() {
        WholeNumberSet cs = WholeNumberSet.EVERY.valuesBeside(n(3), n(2), n(-7));
        // 2c = 7 - 3x: c is whole where x is odd, and then c runs over every number.
        assertTrue(cs.holds(n(2)));
        assertTrue(cs.holds(n(-1)));
        // A negative weight and a shifted constant: c = 5 - x for x in 0..3.
        WholeNumberSet x = WholeNumberSet.ofRuns(WholeNumberRuns.one(n(0), n(3)));
        WholeNumberSet shifted = x.valuesBeside(n(1), n(1), n(-5));
        assertEquals(n(2), shifted.least());
        assertEquals(n(5), shifted.greatest());
        assertTrue(shifted.holds(n(3)));
        assertFalse(shifted.holds(n(6)));
        // s - c + 5 = 0 for s in 0..3: c = s + 5, from five to eight.
        WholeNumberSet turned = x.valuesBeside(n(1), n(-1), n(5));
        assertEquals(n(5), turned.least());
        assertEquals(n(8), turned.greatest());
    }

    /**
     * For every sign and size of the weights and the constant, and every kind of set (bounded,
     * open either way, a remainder or not), {@code c} is one of what is left exactly where the
     * number it fixes is a whole number of the set. The oracle asks the equation of each {@code c}
     * and no run of the answer, so a rounding of an end the wrong way, or a sign carried across a
     * weight, is a {@code c} the two disagree at.
     */
    @Test
    void whatAWeighedEquationLeavesIsTheNumbersWhoseOtherNumberIsInTheSet() {
        Random random = new Random(3146);
        List<String> apart = new ArrayList<>();
        for (int trial = 0; trial < 4000; trial++) {
            BigInteger modulus = n(1 + random.nextInt(6));
            Congruences within = new Congruences(n(random.nextInt(7)), modulus);
            BigInteger from = random.nextInt(4) == 0 ? null : n(random.nextInt(31) - 15);
            BigInteger to = random.nextInt(4) == 0 ? null : n(random.nextInt(31) - 15);
            if (from != null && to != null && from.compareTo(to) > 0) {
                BigInteger swap = from;
                from = to;
                to = swap;
            }
            WholeNumberSet set;
            try {
                set = WholeNumberSet.ofClass(within).and(
                        WholeNumberSet.ofRuns(WholeNumberRuns.one(from, to)));
            } catch (IllegalArgumentException none) {
                continue;
            }
            if (set.isNone()) {
                continue;
            }
            BigInteger weightHere = aWeight(random);
            BigInteger weightThere = aWeight(random);
            BigInteger constant = n(random.nextInt(19) - 9);
            WholeNumberSet left = set.valuesBeside(weightHere, weightThere, constant);
            for (long c = -150; c <= 150; c++) {
                // weightHere·s + weightThere·c + constant = 0
                BigInteger rest = weightThere.multiply(n(c)).add(constant).negate();
                boolean expected = rest.mod(weightHere.abs()).signum() == 0
                        && set.holds(rest.divide(weightHere));
                if (left.holds(n(c)) != expected) {
                    apart.add("s of " + set + ", " + weightHere + "·s + " + weightThere
                            + "·c + " + constant + " = 0 at c = " + c + ": said "
                            + left.holds(n(c)) + ", is " + expected);
                    break;
                }
            }
        }
        assertEquals(List.of(), apart.stream().limit(5).toList());
    }

    /** A set built of several progressions, some of them touching, nested or open: what the
     *  operations leave is what the numbers do, however the parts are joined and dropped. */
    @Test
    void theOperationsAreThoseOfNumbersForSetsOfManyProgressions() {
        Random random = new Random(31461);
        List<String> apart = new ArrayList<>();
        WholeNumberSet.Budget room = parts -> parts <= 512;
        for (int trial = 0; trial < 1500; trial++) {
            WholeNumberSet one = aSetOfSeveral(random);
            WholeNumberSet other = aSetOfSeveral(random);
            WholeNumberSet both = one.and(other, room);
            WholeNumberSet either = one.or(other, room);
            WholeNumberSet not = one.complement(room);
            for (long at = -60; at <= 60; at++) {
                BigInteger number = n(at);
                boolean inOne = one.holds(number);
                boolean inOther = other.holds(number);
                if ((both != null && both.holds(number) != (inOne && inOther))
                        || (either != null && either.holds(number) != (inOne || inOther))
                        || (not != null && not.holds(number) == inOne)) {
                    apart.add(one + " with " + other + " at " + at);
                    break;
                }
            }
        }
        assertEquals(List.of(), apart.stream().limit(3).toList());
    }

    /**
     * The members a set names are those it holds in the window its ends make, in order and each
     * once, and a set with no end one way or more members than the limit names none.
     */
    @Test
    void theMembersAFiniteSetNamesAreThoseItHoldsInOrder() {
        Random random = new Random(314611);
        int finite = 0;
        int tooMany = 0;
        for (int trial = 0; trial < 1500; trial++) {
            WholeNumberSet set = aSetOfSeveral(random);
            List<BigInteger> members = set.membersUpTo(8);
            if (set.least() == null || set.greatest() == null) {
                assertNull(members, set.toString());
                continue;
            }
            List<BigInteger> held = new ArrayList<>();
            for (long at = set.least().longValueExact(); at <= set.greatest().longValueExact();
                    at++) {
                if (set.holds(n(at))) {
                    held.add(n(at));
                }
            }
            if (held.size() > 8) {
                assertNull(members, set.toString());
                tooMany++;
            } else {
                assertEquals(held, members, set.toString());
                finite++;
            }
        }
        assertTrue(finite > 50 && tooMany > 50, finite + " finite, " + tooMany + " too many");
    }

    /** A weight of one to six, either sign. */
    private static BigInteger aWeight(Random random) {
        return n(random.nextBoolean() ? 1 + random.nextInt(6) : -1 - random.nextInt(6));
    }

    private static WholeNumberSet aSetOfSeveral(Random random) {
        WholeNumberSet out = WholeNumberSet.NONE;
        for (int part = 0; part <= random.nextInt(3); part++) {
            Congruences within = new Congruences(n(random.nextInt(5)), n(1 + random.nextInt(4)));
            BigInteger from = random.nextInt(3) == 0 ? null : n(random.nextInt(41) - 20);
            BigInteger to = random.nextInt(3) == 0 ? null : n(random.nextInt(41) - 20);
            if (from != null && to != null && from.compareTo(to) > 0) {
                BigInteger swap = from;
                from = to;
                to = swap;
            }
            WholeNumberSet each = WholeNumberSet.ofClass(within).and(
                    WholeNumberSet.ofRuns(WholeNumberRuns.one(from, to)));
            out = out.or(each);
        }
        return out;
    }

    @Test
    void aWeightOfNoughtLeavesNothingToSolve() {
        assertNull(WholeNumberSet.EVERY.valuesBeside(n(0), n(1), n(0)));
        assertNull(WholeNumberSet.EVERY.valuesBeside(n(1), n(0), n(0)));
    }

    private static final WholeNumberSet.Budget ROOM = parts -> parts <= 64;

    /** A few sets of runs and remainders, none of them written to suit what is asked of it. */
    private static List<WholeNumberSet> family() {
        WholeNumberSet threes = WholeNumberSet.ofClass(new Congruences(BigInteger.ONE, n(3)));
        return List.of(WholeNumberSet.NONE, WholeNumberSet.EVERY, evens(), threes,
                evens().and(nonNegative()),
                threes.and(WholeNumberSet.ofRuns(WholeNumberRuns.one(n(-7), n(20)))),
                WholeNumberSet.ofRuns(WholeNumberRuns.one(n(0), n(0)).or(
                        WholeNumberRuns.one(n(6), null))),
                evens().or(threes),
                evens().and(WholeNumberSet.ofClass(new Congruences(BigInteger.ZERO, n(4)))));
    }

    private static final long LOW = -70;
    private static final long HIGH = 70;

    /** Every operation agrees with the same operation over the numbers, asked of each one. */
    @Test
    void theOperationsAreThoseOfSetsOfNumbers() {
        for (WholeNumberSet one : family()) {
            WholeNumberSet not = one.complement(ROOM);
            assertTrue(not != null);
            for (WholeNumberSet other : family()) {
                WholeNumberSet both = one.and(other, ROOM);
                WholeNumberSet either = one.or(other, ROOM);
                for (long at = LOW; at <= HIGH; at++) {
                    BigInteger number = n(at);
                    assertEquals(!one.holds(number), not.holds(number), "not at " + at);
                    assertEquals(one.holds(number) && other.holds(number), both.holds(number),
                            "and at " + at);
                    assertEquals(one.holds(number) || other.holds(number), either.holds(number),
                            "or at " + at);
                }
            }
        }
    }

    @Test
    void aProgressionHeldByAnotherAndTwoThatTouchAreOneProgression() {
        WholeNumberSet fours = WholeNumberSet.ofClass(new Congruences(BigInteger.ZERO, n(4)));
        assertEquals(1, evens().or(fours, ROOM).parts().size());
        WholeNumberSet low = WholeNumberSet.ofRuns(WholeNumberRuns.one(n(0), n(5)));
        WholeNumberSet high = WholeNumberSet.ofRuns(WholeNumberRuns.one(n(6), n(9)));
        assertEquals(1, low.or(high, ROOM).parts().size());
    }

    /** A complement costs a progression for each remainder, and is refused rather than cut. */
    @Test
    void aComplementTooWideForTheBudgetIsRefusedNotShortened() {
        WholeNumberSet wide = WholeNumberSet.ofClass(new Congruences(BigInteger.ZERO,
                n(1_000_000_000L)));
        assertNull(wide.complement(ROOM));
        assertNull(wide.and(evens(), parts -> false));
        WholeNumberSet sized = WholeNumberSet.ofClass(new Congruences(BigInteger.ZERO, n(10)));
        // The nine other remainders; the two ends a run could have are paid for and not made.
        assertEquals(9, sized.complement(parts -> parts <= 11).parts().size());
        assertNull(sized.complement(parts -> parts <= 10));
    }

    /** The ends of the type, a type being no more than the numbers between them. */
    @Test
    void theEndsOfIntAreMembersWhereTheirRemainderIs() {
        BigInteger least = n(Integer.MIN_VALUE);
        BigInteger greatest = n(Integer.MAX_VALUE);
        WholeNumberSet type = WholeNumberSet.ofRuns(WholeNumberRuns.one(least, greatest));
        WholeNumberSet inType = evens().and(type, ROOM);
        assertTrue(inType.holds(least));
        assertFalse(inType.holds(greatest));
        assertTrue(inType.holds(greatest.subtract(BigInteger.ONE)));
        assertFalse(inType.holds(least.subtract(BigInteger.TWO)));
        assertEquals(least, inType.least());
        assertEquals(greatest.subtract(BigInteger.ONE), inType.greatest());
        WholeNumberSet odds = WholeNumberSet.ofClass(new Congruences(BigInteger.ONE, n(2)));
        assertTrue(odds.and(type, ROOM).holds(greatest));
        assertFalse(odds.and(type, ROOM).holds(least));
    }

    /** A set whose every number lies past the type holds none of the type. */
    @Test
    void aSetOfNoNumberOfTheTypeIsNone() {
        WholeNumberSet type = WholeNumberSet.ofRuns(WholeNumberRuns.one(n(Integer.MIN_VALUE),
                n(Integer.MAX_VALUE)));
        WholeNumberSet past = WholeNumberSet.ofRuns(WholeNumberRuns.one(
                n(Integer.MAX_VALUE).add(BigInteger.ONE), null));
        assertTrue(past.and(type, ROOM).isNone());
        // Odd numbers between nought and nought have none.
        WholeNumberSet nought = WholeNumberSet.ofRuns(WholeNumberRuns.one(BigInteger.ZERO,
                BigInteger.ZERO));
        assertTrue(nought.and(WholeNumberSet.ofClass(new Congruences(BigInteger.ONE, n(2))), ROOM)
                .isNone());
    }

    @Test
    void theNearestMemberSkipsWhatIsExcludedAndStaysInTheSet() {
        WholeNumberSet evensFromTwo = evens().and(WholeNumberSet.ofRuns(
                WholeNumberRuns.one(n(2), null)));
        assertEquals(n(2), evensFromTwo.nearestMember(n(-9), Set.of()));
        assertEquals(n(4), evensFromTwo.nearestMember(n(3), Set.of(n(2))));
        assertEquals(n(6), evensFromTwo.nearestMember(n(3), Set.of(n(2), n(4))));
        WholeNumberSet only = WholeNumberSet.ofRuns(WholeNumberRuns.one(n(5), n(5)));
        assertNull(only.nearestMember(n(0), Set.of(n(5))));
    }

    @Test
    void aRunWithNoMemberOfTheRemainderHoldsNothing() {
        WholeNumberSet oneToOne = WholeNumberSet.ofRuns(WholeNumberRuns.one(n(1), n(1)))
                .and(evens());
        assertTrue(oneToOne.isNone());
    }
}
