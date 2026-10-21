package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.RulesAsWritten.Written;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static souther.compiler.numeric.RulesAsWritten.admits;
import static souther.compiler.numeric.RulesAsWritten.boxed;
import static souther.compiler.numeric.RulesAsWritten.everyOrder;
import static souther.compiler.numeric.RulesAsWritten.pointsSatisfying;
import static souther.compiler.numeric.RulesAsWritten.rules;
import static souther.compiler.numeric.RulesAsWritten.twice;

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
 *
 * <p>The systems are the ones the closure has a step for ({@link #SYSTEMS}): a bound carried onto a
 * position along differences above and below, through more than one position between; a difference
 * read through nought; ends that meet at one value beside ends that cross; a cycle summing to nought
 * beside one summing below it; two rules on one edge with the looser said last; a difference said
 * outright looser than the path to it through a third position, which a closure keeping the first
 * bound it found for an edge leaves loose; and the weights and
 * strict comparisons a rule is read down to the same edges from.
 */
class WhatTheDifferenceBoundsSayIsWhatThePointsSayTest {

    private static final int LOW = -4;
    private static final int HIGH = 4;

    /** Each system with what it is for; every position it names is held to the range. */
    private static final List<List<Written>> SYSTEMS = List.of(
            // A bound above carried onto a through two differences.
            rules("a - b <= 1", "b - c <= 1", "c <= 0"),
            // A bound below carried onto a through two differences.
            rules("c - b <= -1", "b - a <= -1", "c >= 1"),
            // No difference between a and b, so theirs is read through nought.
            rules("a <= 1", "b >= 2"),
            // Two ends at one value, which leave it.
            rules("a >= 3", "a <= 3"),
            // Two ends that have crossed.
            rules("a >= 3", "a <= 2"),
            // A cycle summing to nought, which leaves a and b equal.
            rules("a - b <= 0", "b - a <= 0"),
            // A cycle summing below nought.
            rules("a - b <= -1", "b - a <= 0"),
            // Ends crossed only once a bound is carried along a difference.
            rules("a - b <= -3", "b <= -2", "c - a <= 0"),
            // Two bounds on one difference, the looser said last.
            rules("a - b <= 1", "a - b <= 3"),
            // A difference said outright looser than the path to it through a third position.
            rules("a - c <= 3", "a - b <= 0", "b - c <= 0"),
            // Weights of two and strict comparisons, which are read down to edges of one.
            rules("2a - 2b <= 3", "2c >= 3", "a < 0", "b - c < 2"),
            // A bound carried onto a through three positions between.
            rules("a - b <= 0", "b - c <= 0", "c - d <= 0", "d <= 1"));

    private static List<String> positionsOf(List<Written> system) {
        return List.copyOf(RulesAsWritten.positionsOf(system));
    }

    private static List<Written> bounded(List<Written> system) {
        return boxed(system, positionsOf(system), LOW, HIGH);
    }

    private static DifferenceBounds<String> closed(List<Written> written) {
        return DifferenceBounds.over(RulesAsWritten.read(written, atom -> Granularity.DISCRETE),
                CanonicalOrder.asTheyAreSpelled());
    }

    @Test
    void everyClosureAgreesWithTheePointsItIsAbout() {
        int empties = 0;
        for (List<Written> system : SYSTEMS) {
            List<Written> written = bounded(system);
            List<String> positions = positionsOf(system);
            DifferenceBounds<String> closed = closed(written);
            List<Map<String, Integer>> admitted = pointsSatisfying(written, positions, LOW, HIGH);

            if (admitted.isEmpty()) {
                empties++;
            }
            assertEquals(admitted.isEmpty(), closed.holdsNothing(),
                    () -> "decided: " + written + " admits " + admitted.size() + " points");
            if (admitted.isEmpty()) {
                continue;   // nothing is left, so there is no bound to be sound or tight about
            }
            assertSoundAndTight(written, positions, closed, admitted);
        }
        int empty = empties;
        assertTrue(empties > 0 && empties < SYSTEMS.size(),
                () -> "the systems have to come out both ways to check both, and " + empty
                        + " of " + SYSTEMS.size() + " were empty");
    }

    /**
     * The same rules in any order are the same answers.
     *
     * <p>Every order of a system's own rules, said after the range and before it. The range holds a
     * position each and nothing between two, so where it stands against the rules is the one thing
     * about its order a reader could answer differently for.
     */
    @Test
    void theOrderTheRulesArrivedInIsNotPartOfTheAnswer() {
        for (List<Written> system : SYSTEMS) {
            List<Written> written = bounded(system);
            DifferenceBounds<String> asWritten = closed(written);
            List<Written> range = written.subList(0, written.size() - system.size());
            for (List<Written> order : everyOrder(system)) {
                List<Written> rangeFirst = new ArrayList<>(range);
                rangeFirst.addAll(order);
                List<Written> rangeLast = new ArrayList<>(order);
                rangeLast.addAll(range);
                assertSameAnswers(rangeFirst, asWritten, closed(rangeFirst));
                assertSameAnswers(rangeLast, asWritten, closed(rangeLast));
            }
        }
    }

    /** And asserting a rule twice says what asserting it once says. */
    @Test
    void sayingARuleTwiceSaysWhatSayingItOnceSays() {
        for (List<Written> system : SYSTEMS) {
            List<Written> written = bounded(system);
            assertSameAnswers(written, closed(written), closed(twice(written)));
        }
    }

    private static void assertSameAnswers(List<Written> written, DifferenceBounds<String> one,
                                          DifferenceBounds<String> other) {
        assertEquals(one.holdsNothing(), other.holdsNothing(), written::toString);
        if (one.holdsNothing()) {
            return;   // where nothing is left there is no tightest bound to compare
        }
        List<String> positions = positionsOf(written);
        for (String position : positions) {
            assertEquals(one.upperBoundOf(position), other.upperBoundOf(position),
                    () -> "upper bound of " + position + " moved under " + written);
            assertEquals(one.lowerBoundOf(position), other.lowerBoundOf(position),
                    () -> "lower bound of " + position + " moved under " + written);
            for (String apart : positions) {
                assertEquals(one.differenceBound(position, apart),
                        other.differenceBound(position, apart),
                        () -> position + " - " + apart + " moved under " + written);
            }
        }
    }

    private static void assertSoundAndTight(List<Written> written, List<String> positions,
                                            DifferenceBounds<String> closed,
                                            List<Map<String, Integer>> admitted) {
        for (String position : positions) {
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

            for (String other : positions) {
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
}
