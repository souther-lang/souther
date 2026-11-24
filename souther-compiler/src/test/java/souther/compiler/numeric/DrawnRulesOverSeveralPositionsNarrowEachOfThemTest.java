package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.AffineReduction.Reduction;
import souther.compiler.numeric.RulesAsWritten.Written;
import souther.test.Nightly;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static souther.compiler.numeric.RulesAsWritten.pointsSatisfying;
import static souther.compiler.numeric.RulesAsWritten.someRuleHoldsNever;

/**
 * Rules over several positions, drawn at random, narrow each of them and never past what the rules
 * admit.
 *
 * <p>The claim is {@code ARuleOverSeveralPositionsNarrowsEachOfThemTest}'s: a narrower box never
 * says less. That no point the rules admit is refused, and that the answer is the same whatever
 * order the rules arrived in, are asked of rules drawn at random for every reader of rules, this
 * one among them, in {@code EveryReaderOfDrawnRulesAnswersByTheRulesAloneTest}. What this adds is
 * the rules: the chosen systems are written for the steps the reduction takes, and these are drawn
 * over every weight from minus three to three on each of three positions, every relation, and every
 * threshold in the range, which reaches combinations no chosen system names. The seeds are fixed, so
 * a round that fails is the same round when it is run again.
 *
 * <p>A draw comes now and then to a rule no value satisfies, a weighted equality whose threshold the
 * weights cannot reach. There is no constraint to hand on for it, and what is owed instead is that
 * the points hold nothing either, which is asked before the round is passed over.
 *
 * <p>Nightly, for what it costs: hundreds of draws, each enumerated over the whole range. No cheaper
 * way asks whether a step the chosen systems do not name goes wrong somewhere among the
 * combinations, and what it finds is as well found by the morning as by the change that caused it,
 * since the chosen systems stand in the run every change waits on.
 */
@Nightly
class DrawnRulesOverSeveralPositionsNarrowEachOfThemTest {

    private static final List<String> POSITIONS = List.of("a", "b", "c");
    private static final int LOW = -4;
    private static final int HIGH = 4;
    private static final int CASES = 300;

    private static ExactRatio num(long whole) {
        return ExactRatio.of(whole);
    }

    private static Box<String> between(int low, int high) {
        Map<String, ExactCut> least = new LinkedHashMap<>();
        Map<String, ExactCut> most = new LinkedHashMap<>();
        for (String position : POSITIONS) {
            least.put(position, ExactCut.inclusive(num(low)));
            most.put(position, ExactCut.inclusive(num(high)));
        }
        return new Box<>(least, most);
    }

    /** The rules read against {@code from}, or null where the differences alone already hold
     *  nothing, which is where a round is never reached. */
    private static FormReach<String> reading(List<AffineConstraint<String>> rules, Box<String> from) {
        DifferenceBounds<String> differences =
                DifferenceBounds.over(rules, CanonicalOrder.asTheyAreSpelled());
        return differences.holdsNothing() ? null
                : FormReach.over(rules, from, differences, CanonicalOrder.asTheyAreSpelled());
    }

    private static Reduction<String> reduced(FormReach<String> reading) {
        return AffineReduction.over(reading, atom -> Granularity.DISCRETE,
                CanonicalOrder.asTheyAreSpelled());
    }

    /** Monotone: a narrower box never yields a wider answer. */
    @Test
    void aNarrowerBoxNeverSaysLess() {
        Random dice = new Random(600);
        for (int round = 0; round < CASES; round++) {
            List<Written> written = someRules(dice);
            if (heldNowhere(written)) {
                continue;
            }
            List<AffineConstraint<String>> stated = read(written);
            FormReach<String> readWide = reading(stated, between(LOW, HIGH));
            FormReach<String> readNarrow = reading(stated, between(LOW + 1, HIGH - 1));
            if (readWide == null || readNarrow == null) {
                continue;   // the differences hold nothing, which the closure answers before a round
            }
            if (!(reduced(readWide) instanceof Reduction.Tightened<String> loose)) {
                continue;   // the wider box was already empty, so there is nothing wider to be
            }
            if (!(reduced(readNarrow) instanceof Reduction.Tightened<String> tight)) {
                continue;
            }
            for (String position : POSITIONS) {
                ExactCut looseHigh = loose.atMost().get(position);
                ExactCut tightHigh = tight.atMost().get(position);
                if (looseHigh != null && tightHigh != null) {
                    assertEquals(tightHigh, ExactCut.tighterUpper(looseHigh, tightHigh),
                            () -> "a narrower box said less above " + position);
                }
                ExactCut looseLow = loose.atLeast().get(position);
                ExactCut tightLow = tight.atLeast().get(position);
                if (looseLow != null && tightLow != null) {
                    assertEquals(tightLow, ExactCut.tighterLower(looseLow, tightLow),
                            () -> "a narrower box said less below " + position);
                }
            }
        }
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

    /** Rules over two or three positions, weighted unevenly, which is what the difference bounds
     *  cannot hold and what the reduction exists for. */
    private static List<Written> someRules(Random dice) {
        List<Written> out = new ArrayList<>();
        int howMany = 1 + dice.nextInt(3);
        for (int i = 0; i < howMany; i++) {
            Map<String, ExactRatio> coefs = new LinkedHashMap<>();
            for (String position : POSITIONS) {
                int weight = dice.nextInt(7) - 3;
                if (weight != 0) {
                    coefs.put(position, num(weight));
                }
            }
            if (coefs.isEmpty()) {
                continue;
            }
            long constant = dice.nextInt(21) - 10L;
            out.add(new Written(coefs, num(constant), someRelation(dice)));
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
