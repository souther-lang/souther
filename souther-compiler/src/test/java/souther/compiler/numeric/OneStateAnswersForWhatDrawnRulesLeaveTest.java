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
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static souther.compiler.numeric.RulesAsWritten.admits;
import static souther.compiler.numeric.RulesAsWritten.boxed;
import static souther.compiler.numeric.RulesAsWritten.pointsSatisfying;
import static souther.compiler.numeric.RulesAsWritten.someRuleHoldsNever;

/**
 * One state answers for what rules drawn at random leave.
 *
 * <p>The claims are {@code OneStateAnswersForWhatTheRulesLeaveTest}'s — the state is the same
 * whatever order the rules arrived in and however often each was said, and no point the rules admit
 * is left outside it — and so is the oracle, every point of a bounded range. What this adds is the
 * rules: the chosen systems there are written for the steps the closure takes, and these are drawn
 * over weights from minus two to two on each of three positions, every relation, and every threshold
 * in the range, which reaches combinations no chosen system names. The seeds are fixed, so a round
 * that fails is the same round when it is run again.
 *
 * <p>A draw comes now and then to a rule no value satisfies, a weighted equality whose threshold the
 * weights cannot reach. There is no constraint to hand on for it, and what is owed instead is that
 * the points hold nothing either, which is asked before the round is passed over.
 *
 * <p>Nightly, for what it costs: hundreds of draws, each closed and enumerated over the whole range.
 * No cheaper way asks whether a step the chosen systems do not name goes wrong somewhere among the
 * combinations, and what it finds is as well found by the morning as by the change that caused it,
 * since the chosen systems stand in the run every change waits on.
 */
@Nightly
class OneStateAnswersForWhatDrawnRulesLeaveTest {

    private static final List<String> POSITIONS = List.of("a", "b", "c");
    private static final int LOW = -4;
    private static final int HIGH = 4;
    private static final int CASES = 300;

    private static ExactRatio num(long whole) {
        return ExactRatio.of(whole);
    }

    private static ClosedState<String> closing(List<AffineConstraint<String>> rules) {
        return ClosedState.of(rules, atom -> Granularity.DISCRETE,
                CanonicalOrder.asTheyAreSpelled());
    }

    @Test
    void theOrderTheRulesArrivedInIsNotPartOfTheAnswer() {
        Random dice = new Random(891);
        for (int round = 0; round < CASES; round++) {
            List<Written> written = someRules(dice);
            if (heldNowhere(written)) {
                continue;
            }
            List<AffineConstraint<String>> stated = read(written);
            List<AffineConstraint<String>> shuffled = new ArrayList<>(stated);
            Collections.shuffle(shuffled, dice);

            ClosedState<String> asWritten = closing(stated);
            ClosedState<String> reordered = closing(shuffled);
            assertEquals(asWritten.holdsNothing(), reordered.holdsNothing(),
                    () -> "emptiness moved when the rules were reordered: " + stated);
            if (asWritten.holdsNothing()) {
                continue;
            }
            assertEquals(asWritten.box(), reordered.box(),
                    () -> "the box moved when the rules were reordered: " + stated);
        }
    }

    @Test
    void sayingARuleTwiceSaysWhatSayingItOnceSays() {
        Random dice = new Random(1016);
        for (int round = 0; round < CASES; round++) {
            List<Written> written = someRules(dice);
            if (heldNowhere(written)) {
                continue;
            }
            List<AffineConstraint<String>> stated = read(written);
            List<AffineConstraint<String>> doubled = new ArrayList<>(stated);
            doubled.addAll(stated);
            ClosedState<String> once = closing(stated);
            ClosedState<String> twice = closing(doubled);
            assertEquals(once.holdsNothing(), twice.holdsNothing());
            if (!once.holdsNothing()) {
                assertEquals(once.box(), twice.box());
            }
        }
    }

    @Test
    void noPointTheRulesAdmitIsEverRefused() {
        Random dice = new Random(4800);
        int narrowed = 0;
        int empties = 0;
        for (int round = 0; round < CASES; round++) {
            // Every position bounded to the range, so the points enumerated are all the points.
            List<Written> written = boxed(someRules(dice), POSITIONS, LOW, HIGH);
            if (heldNowhere(written)) {
                continue;
            }
            List<Map<String, Integer>> admitted = pointsSatisfying(written, POSITIONS, LOW, HIGH);
            ClosedState<String> closed = closing(read(written));

            if (admitted.isEmpty()) {
                empties++;
                continue;   // emptiness is proven one way only, so nothing is owed here
            }
            assertFalse(closed.holdsNothing(),
                    () -> "said nothing is left, but " + written + " admits " + admitted.size());
            // A box holds every admitted point exactly when, at each position, it holds the least
            // and the greatest value an admitted point has there — so those two points are the
            // ones asked about.
            for (String position : POSITIONS) {
                Map<String, Integer> lowest = admitted.getFirst();
                Map<String, Integer> highest = admitted.getFirst();
                for (Map<String, Integer> point : admitted) {
                    if (point.get(position) < lowest.get(position)) {
                        lowest = point;
                    }
                    if (point.get(position) > highest.get(position)) {
                        highest = point;
                    }
                }
                for (Map<String, Integer> point : List.of(lowest, highest)) {
                    ExactRatio at = num(point.get(position));
                    assertTrue(admits(closed.box().leastOf(position), at, false)
                                    && admits(closed.box().mostOf(position), at, true),
                            () -> "refused a point the rules admit: " + point + " under " + written
                                    + " left " + position + " in ["
                                    + closed.box().leastOf(position) + ", "
                                    + closed.box().mostOf(position) + "]");
                }
            }
            for (String position : POSITIONS) {
                if (closed.box().mostOf(position) != null
                        && closed.box().mostOf(position).at().compareTo(num(HIGH)) < 0) {
                    narrowed++;
                }
            }
        }
        assertTrue(narrowed > 0 && empties > 0,
                "narrowed " + narrowed + " and " + empties + " were empty, so this checked little");
    }

    /** Whether a drawn rule holds at no value, in which case the points must hold nothing too and
     *  there is nothing to hand on. */
    private static boolean heldNowhere(List<Written> written) {
        if (!someRuleHoldsNever(written, atom -> Granularity.DISCRETE)) {
            return false;
        }
        assertEquals(List.of(), pointsSatisfying(written, POSITIONS, LOW, HIGH),
                () -> "a rule of " + written + " was read as holding nowhere, and points satisfy it");
        return true;
    }

    private static List<Written> someRules(Random dice) {
        List<Written> out = new ArrayList<>();
        int howMany = 1 + dice.nextInt(3);
        for (int i = 0; i < howMany; i++) {
            Map<String, ExactRatio> coefs = new LinkedHashMap<>();
            for (String position : POSITIONS) {
                int weight = dice.nextInt(5) - 2;
                if (weight != 0) {
                    coefs.put(position, num(weight));
                }
            }
            if (coefs.isEmpty()) {
                continue;
            }
            out.add(new Written(coefs, num(dice.nextInt(15) - 7), someRelation(dice)));
        }
        return out;
    }

    /** One of the relations a rule can be written with, taken from the enum, so that a relation
     *  added to the language is drawn here without anyone remembering to add it. */
    private static Rel someRelation(Random dice) {
        Rel[] all = Rel.values();
        return all[dice.nextInt(all.length)];
    }

    private static List<AffineConstraint<String>> read(List<Written> written) {
        return RulesAsWritten.read(written, atom -> Granularity.DISCRETE);
    }
}
