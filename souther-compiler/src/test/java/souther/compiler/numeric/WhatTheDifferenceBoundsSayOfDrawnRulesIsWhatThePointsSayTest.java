package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.RulesAsWritten.Written;
import souther.test.Nightly;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static souther.compiler.numeric.RulesAsWritten.admits;
import static souther.compiler.numeric.RulesAsWritten.pointsSatisfying;

/**
 * What the difference bounds say is what the points say, over systems drawn at random.
 *
 * <p>The claims are {@code WhatTheDifferenceBoundsSayIsWhatThePointsSayTest}'s — sound, decided and
 * tight against every point of a bounded range, and the same whatever order the rules arrived in or
 * however often each was said — and so is the oracle. What this adds is the systems: the chosen ones
 * there are written for the steps the closure takes, and these are drawn from the shapes the
 * fragment has, a bound or a difference on any of three positions, weighed by one or two, strict or
 * not, at any threshold in the range. A combination no chosen system names is one a draw can reach.
 * The seeds are fixed, so a round that fails is the same round when it is run again.
 *
 * <p>Nightly, for what it costs: hundreds of systems, each enumerated over the whole range. No
 * cheaper way asks what it asks, which is whether a step the chosen systems do not name goes wrong
 * somewhere among the combinations, and what it finds is as well found by the morning as by the
 * change that caused it, since the chosen systems stand in the run every change waits on.
 */
@Nightly
class WhatTheDifferenceBoundsSayOfDrawnRulesIsWhatThePointsSayTest {

    private static final List<String> POSITIONS = List.of("a", "b", "c");
    private static final int LOW = -4;
    private static final int HIGH = 4;
    private static final int CASES = 300;

    private static DifferenceBounds<String> closed(List<AffineConstraint<String>> stated) {
        return DifferenceBounds.over(stated, CanonicalOrder.asTheyAreSpelled());
    }

    @Test
    void everyClosureAgreesWithTheePointsItIsAbout() {
        Random dice = new Random(891);
        int empties = 0;
        for (int round = 0; round < CASES; round++) {
            List<Written> written = aSystem(dice);
            DifferenceBounds<String> closed = closed(read(written));
            List<Map<String, Integer>> admitted = pointsSatisfying(written, POSITIONS, LOW, HIGH);

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
            DifferenceBounds<String> asWritten = closed(stated);
            List<AffineConstraint<String>> shuffled = new ArrayList<>(stated);
            Collections.shuffle(shuffled, dice);
            DifferenceBounds<String> reordered = closed(shuffled);

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
            DifferenceBounds<String> once = closed(stated);
            DifferenceBounds<String> twice = closed(doubled);
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
            ExactCut high = closed.upperBoundOf(position);
            ExactCut low = closed.lowerBoundOf(position);
            int most = admitted.stream().mapToInt(point -> point.get(position)).max().orElseThrow();
            int least = admitted.stream().mapToInt(point -> point.get(position)).min().orElseThrow();

            assertTrue(admits(high, ExactRatio.of(most), true),
                    () -> "unsound: " + written + " admits " + position + " = " + most
                            + " and the closure says " + high);
            assertTrue(admits(low, ExactRatio.of(least), false),
                    () -> "unsound: " + written + " admits " + position + " = " + least
                            + " and the closure says >= " + low);
            assertEquals(ExactCut.inclusive(ExactRatio.of(most)), high,
                    () -> "not tight above at " + position + " for " + written);
            assertEquals(ExactCut.inclusive(ExactRatio.of(least)), low,
                    () -> "not tight below at " + position + " for " + written);

            for (String other : POSITIONS) {
                if (position.equals(other)) {
                    continue;
                }
                ExactCut apart = closed.differenceBound(position, other);
                int widest = admitted.stream()
                        .mapToInt(point -> point.get(position) - point.get(other))
                        .max().orElseThrow();
                assertTrue(admits(apart, ExactRatio.of(widest), true),
                        () -> "unsound: " + written + " admits " + position + " - " + other
                                + " = " + widest + " and the closure says " + apart);
                assertEquals(ExactCut.inclusive(ExactRatio.of(widest)), apart,
                        () -> "not tight on " + position + " - " + other + " for " + written);
            }
        }
    }

    /**
     * A handful of rules of this fragment's shapes, over positions every one of which is bounded to
     * the range the points are enumerated over — so the points are all the points there are. Every
     * rule a draw makes states a constraint, so the reading refuses none of them.
     */
    private static List<Written> aSystem(Random dice) {
        List<Written> out = new ArrayList<>();
        for (String position : POSITIONS) {
            out.add(new Written(Map.of(position, ExactRatio.ONE),
                    ExactRatio.of(-LOW), Rel.GE));
            out.add(new Written(Map.of(position, ExactRatio.ONE), ExactRatio.of(-HIGH), Rel.LE));
        }
        int howMany = 2 + dice.nextInt(4);
        for (int i = 0; i < howMany; i++) {
            String one = POSITIONS.get(dice.nextInt(POSITIONS.size()));
            long threshold = LOW + (long) dice.nextInt(HIGH - LOW + 1);
            boolean strict = dice.nextBoolean();
            if (dice.nextBoolean()) {
                Rel rel = dice.nextBoolean()
                        ? (strict ? Rel.LT : Rel.LE) : (strict ? Rel.GT : Rel.GE);
                // A weight of two as often as one, so the shape canonicalisation brought in is
                // exercised rather than assumed.
                long weight = dice.nextBoolean() ? 1 : 2;
                out.add(new Written(Map.of(one, ExactRatio.of(weight)),
                        ExactRatio.of(-threshold * weight), rel));
            } else {
                String other = POSITIONS.get(dice.nextInt(POSITIONS.size()));
                if (one.equals(other)) {
                    continue;
                }
                long weight = dice.nextBoolean() ? 1 : 2;
                Map<String, ExactRatio> coefs = new LinkedHashMap<>();
                coefs.put(one, ExactRatio.of(weight));
                coefs.put(other, ExactRatio.of(-weight));
                out.add(new Written(coefs, ExactRatio.of(-threshold * weight),
                        strict ? Rel.LT : Rel.LE));
            }
        }
        return out;
    }

    private static List<AffineConstraint<String>> read(List<Written> written) {
        return RulesAsWritten.read(written, atom -> Granularity.DISCRETE);
    }
}
