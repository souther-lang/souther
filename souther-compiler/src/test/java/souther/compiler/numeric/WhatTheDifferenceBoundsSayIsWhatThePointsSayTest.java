package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.AffineConstraint.Read;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Everything the closure says is checked against the points themselves.
 *
 * <p>Enumerated and not sampled. Every position is bounded to a small range as part of the system,
 * so the points inside that range are all the points there are — which makes "nothing satisfies
 * this" a thing the enumeration decides rather than a thing it fails to find a counterexample to.
 * A check that only looked for counterexamples could not tell an empty system from one whose
 * solutions it did not happen to try.
 *
 * <p>Three claims, and the second is the one the whole arrangement turns on.
 *
 * <pre>
 *     sound        every point the rules admit lies inside every bound derived
 *     decided      it says nothing is left exactly where nothing is left
 *     tight        each bound is reached by some point the rules admit
 * </pre>
 *
 * <p>Soundness alone would be satisfied by deriving nothing. Being decided is what says the closure
 * finds a contradiction whenever the rules hold one — for this fragment, where that is a theorem —
 * so a path that reaches no value cannot come back looking satisfiable. Tightness is what says the
 * bounds are the rules' own and not merely implied by them.
 *
 * <p>And the same answers whatever order the rules arrived in, which is the property this whole
 * arrangement exists to restore.
 */
class WhatTheDifferenceBoundsSayIsWhatThePointsSayTest {

    private static final List<String> POSITIONS = List.of("a", "b", "c");
    private static final int LOW = -4;
    private static final int HIGH = 4;
    private static final int CASES = 300;

    private record Written(Map<String, Rational> coefs, Rational constant, Rel rel) {}

    @Test
    void everyClosureAgreesWithTheePointsItIsAbout() {
        Random dice = new Random(891);
        int empties = 0;
        for (int round = 0; round < CASES; round++) {
            List<Written> written = aSystem(dice);
            List<AffineConstraint<String>> stated = read(written);
            DifferenceBounds<String> closed = DifferenceBounds.over(stated);
            List<Map<String, Integer>> admitted = pointsSatisfying(written);

            if (admitted.isEmpty()) {
                empties++;
            }
            assertEquals(admitted.isEmpty(), closed.holdsNothing(),
                    () -> "decided: " + written + " admits " + admitted.size() + " points");
            if (admitted.isEmpty()) {
                continue;   // nothing is left, so there is no bound to be sound or tight about
            }
            assertSoundAndTight(written, closed, admitted);
        }
        assertTrue(empties > 20 && empties < CASES - 20,
                "the systems have to come out both ways to check both, and " + empties
                        + " of " + CASES + " were empty");
    }

    /** The same rules in any order are the same answers. */
    @Test
    void theOrderTheRulesArrivedInIsNotPartOfTheAnswer() {
        Random dice = new Random(1016);
        for (int round = 0; round < CASES; round++) {
            List<AffineConstraint<String>> stated = read(aSystem(dice));
            DifferenceBounds<String> asWritten = DifferenceBounds.over(stated);
            List<AffineConstraint<String>> shuffled = new ArrayList<>(stated);
            Collections.shuffle(shuffled, dice);
            DifferenceBounds<String> reordered = DifferenceBounds.over(shuffled);

            assertEquals(asWritten.holdsNothing(), reordered.holdsNothing());
            if (asWritten.holdsNothing()) {
                continue;   // where nothing is left there is no tightest bound to compare
            }
            for (String position : POSITIONS) {
                assertEquals(asWritten.upperBoundOf(position), reordered.upperBoundOf(position),
                        () -> "upper bound of " + position + " moved when the rules were reordered");
                assertEquals(asWritten.lowerBoundOf(position), reordered.lowerBoundOf(position),
                        () -> "lower bound of " + position + " moved when the rules were reordered");
                for (String other : POSITIONS) {
                    assertEquals(asWritten.differenceBound(position, other),
                            reordered.differenceBound(position, other));
                }
            }
        }
    }

    /** And asserting a rule twice says what asserting it once says. */
    @Test
    void sayingARuleTwiceSaysWhatSayingItOnceSays() {
        Random dice = new Random(4800);
        for (int round = 0; round < CASES; round++) {
            List<AffineConstraint<String>> stated = read(aSystem(dice));
            List<AffineConstraint<String>> doubled = new ArrayList<>(stated);
            doubled.addAll(stated);
            DifferenceBounds<String> once = DifferenceBounds.over(stated);
            DifferenceBounds<String> twice = DifferenceBounds.over(doubled);
            assertEquals(once.holdsNothing(), twice.holdsNothing());
            if (once.holdsNothing()) {
                continue;
            }
            for (String position : POSITIONS) {
                assertEquals(once.upperBoundOf(position), twice.upperBoundOf(position));
                assertEquals(once.lowerBoundOf(position), twice.lowerBoundOf(position));
            }
        }
    }

    private static void assertSoundAndTight(List<Written> written, DifferenceBounds<String> closed,
                                            List<Map<String, Integer>> admitted) {
        for (String position : POSITIONS) {
            RationalCut high = closed.upperBoundOf(position);
            RationalCut low = closed.lowerBoundOf(position);
            int most = admitted.stream().mapToInt(point -> point.get(position)).max().orElseThrow();
            int least = admitted.stream().mapToInt(point -> point.get(position)).min().orElseThrow();

            assertTrue(admits(high, Rational.of(most), true),
                    () -> "unsound: " + written + " admits " + position + " = " + most
                            + " and the closure says " + high);
            assertTrue(admits(low, Rational.of(least), false),
                    () -> "unsound: " + written + " admits " + position + " = " + least
                            + " and the closure says >= " + low);
            assertEquals(RationalCut.inclusive(Rational.of(most)), high,
                    () -> "not tight above at " + position + " for " + written);
            assertEquals(RationalCut.inclusive(Rational.of(least)), low,
                    () -> "not tight below at " + position + " for " + written);

            for (String other : POSITIONS) {
                if (position.equals(other)) {
                    continue;
                }
                RationalCut apart = closed.differenceBound(position, other);
                int widest = admitted.stream()
                        .mapToInt(point -> point.get(position) - point.get(other))
                        .max().orElseThrow();
                assertTrue(admits(apart, Rational.of(widest), true),
                        () -> "unsound: " + written + " admits " + position + " - " + other
                                + " = " + widest + " and the closure says " + apart);
                assertEquals(RationalCut.inclusive(Rational.of(widest)), apart,
                        () -> "not tight on " + position + " - " + other + " for " + written);
            }
        }
    }

    private static boolean admits(RationalCut cut, Rational value, boolean above) {
        if (cut == null) {
            return true;
        }
        int order = value.compareTo(cut.at());
        int outside = above ? 1 : -1;
        return order != outside * 1 && (order != 0 || cut.inclusive());
    }

    /**
     * A handful of rules of this fragment's shapes, over positions every one of which is bounded to
     * the range the points are enumerated over — so the points are all the points there are.
     */
    private static List<Written> aSystem(Random dice) {
        List<Written> out = new ArrayList<>();
        for (String position : POSITIONS) {
            out.add(new Written(Map.of(position, Rational.of(-LOW == 0 ? 1 : 1)),
                    Rational.of(-LOW), Rel.GE));
            out.add(new Written(Map.of(position, Rational.ONE), Rational.of(-HIGH), Rel.LE));
        }
        int howMany = 2 + dice.nextInt(4);
        for (int i = 0; i < howMany; i++) {
            String one = POSITIONS.get(dice.nextInt(POSITIONS.size()));
            long threshold = LOW + dice.nextInt(HIGH - LOW + 1);
            boolean strict = dice.nextBoolean();
            if (dice.nextBoolean()) {
                Rel rel = dice.nextBoolean()
                        ? (strict ? Rel.LT : Rel.LE) : (strict ? Rel.GT : Rel.GE);
                // A weight of two as often as one, so the shape canonicalisation brought in is
                // exercised rather than assumed.
                long weight = dice.nextBoolean() ? 1 : 2;
                out.add(new Written(Map.of(one, Rational.of(weight)),
                        Rational.of(-threshold * weight), rel));
            } else {
                String other = POSITIONS.get(dice.nextInt(POSITIONS.size()));
                if (one.equals(other)) {
                    continue;
                }
                long weight = dice.nextBoolean() ? 1 : 2;
                Map<String, Rational> coefs = new LinkedHashMap<>();
                coefs.put(one, Rational.of(weight));
                coefs.put(other, Rational.of(-weight));
                out.add(new Written(coefs, Rational.of(-threshold * weight),
                        strict ? Rel.LT : Rel.LE));
            }
        }
        return out;
    }

    private static List<AffineConstraint<String>> read(List<Written> written) {
        List<AffineConstraint<String>> out = new ArrayList<>();
        for (Written each : written) {
            Read<String> read = AffineConstraint.of(each.coefs(), each.constant(), each.rel(),
                    atom -> Granularity.DISCRETE);
            if (read instanceof Read.Stated<String> stated) {
                out.add(stated.constraint());
            }
        }
        return out;
    }

    /** Every whole-numbered point in the range that satisfies every rule as it was written. */
    private static List<Map<String, Integer>> pointsSatisfying(List<Written> written) {
        List<Map<String, Integer>> out = new ArrayList<>();
        for (int a = LOW; a <= HIGH; a++) {
            for (int b = LOW; b <= HIGH; b++) {
                for (int c = LOW; c <= HIGH; c++) {
                    Map<String, Integer> point = new LinkedHashMap<>();
                    point.put("a", a);
                    point.put("b", b);
                    point.put("c", c);
                    if (written.stream().allMatch(rule -> holdsAt(rule, point))) {
                        out.add(point);
                    }
                }
            }
        }
        return out;
    }

    private static boolean holdsAt(Written rule, Map<String, Integer> point) {
        Rational total = rule.constant();
        for (Map.Entry<String, Rational> each : rule.coefs().entrySet()) {
            total = total.plus(each.getValue().times(Rational.of(point.get(each.getKey()))));
        }
        int sign = total.signum();
        return switch (rule.rel()) {
            case LE -> sign <= 0;
            case LT -> sign < 0;
            case GE -> sign >= 0;
            case GT -> sign > 0;
            case EQ -> sign == 0;
            case NE -> sign != 0;
        };
    }
}
