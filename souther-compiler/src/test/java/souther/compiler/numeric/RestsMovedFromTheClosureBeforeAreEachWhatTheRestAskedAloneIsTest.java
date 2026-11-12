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
 * What a closure's first round asks of the premises, worked from the closure of the rules before,
 * is what it is asked alone.
 *
 * <p>The closure of rules with others after them starts from the work the closure of the rules
 * before left ({@link RoundWork}) and moves each premise's answer to its own ends. Every answer is
 * held to {@link FormReach#leastOfTheRestOf} asked of the rest by itself, and the moved premises
 * are counted so that a test that moved none is not read as one that held.
 *
 * <p>The ends are drawn apart: one position's ends changed, several, one coming where it was
 * missing or going where it was held, one changing only in whether it is reached. Several moved
 * positions are more than the work is moved over, so the closure after them is worked in full, which
 * is the answer held to as well. The seeds are fixed, so a round that fails is the same round when
 * it is run again.
 */
class RestsMovedFromTheClosureBeforeAreEachWhatTheRestAskedAloneIsTest {

    private static final List<String> POSITIONS = List.of("a", "b", "cc", "d", "e");

    private static final int CASES = 500;

    @Test
    void everyRestOfARuleSaidAfterIsWhatItIsAskedAlone() {
        Random dice = new Random(31670);
        long carried = 0;
        int asked = 0;
        for (int round = 0; round < CASES; round++) {
            CanonicalOrder<String> order = RulesNamingNoPositionInCommonCloseApartTest.ORDERS
                    .get(round % RulesNamingNoPositionInCommonCloseApartTest.ORDERS.size());
            List<AffineConstraint<String>> before = read(someRules(dice, 2 + dice.nextInt(4)));
            List<AffineConstraint<String>> after = new ArrayList<>(before);
            after.addAll(read(someRules(dice, 1 + dice.nextInt(2))));
            if (DifferenceBounds.over(before, order).holdsNothing()
                    || DifferenceBounds.over(after, order).holdsNothing()) {
                continue;
            }
            Box<String> start = someEnds(dice);
            Box<String> later = movedEnds(dice, start);

            RoundWork<String> parent = new RoundWork<>(before, start);
            FormReach<String> first = FormReach.over(before, start,
                    DifferenceBounds.over(before, order), order).working(List.of(), parent);
            askEveryRest(first, before, order);

            DifferenceBounds<String> differences = DifferenceBounds.over(after, order);
            FormReach<String> alone = FormReach.over(after, later, differences, order);
            FormReach<String> moved = FormReach.over(after, later, differences, order)
                    .working(List.of(parent), new RoundWork<>(after, later));
            for (AffineConstraint<String> rule : after) {
                Map<String, ExactRatio> whole = rule.form().coefs();
                assertEquals(alone.of(whole, ExactRatio.ZERO), moved.ofKept(rule, whole),
                        "the form of " + rule + " under " + after + " from " + before + ", ends "
                                + start + " then " + later);
                for (AffineConstraint.HalfSpace<String> half : rule.halfSpaces()) {
                    FormReach<String>.Rests rests = moved.rests(rule, half);
                    for (String atom : half.form().atomsIn(order)) {
                        Map<String, ExactRatio> rest = new LinkedHashMap<>(half.form().coefs());
                        rest.remove(atom);
                        assertEquals(alone.leastOfTheRestOf(rule, rest, ExactRatio.ZERO),
                                rests.leastOfTheRest(atom),
                                "the rest of " + atom + " in " + half + " under " + after
                                        + " from " + before + ", ends " + start + " then " + later);
                        asked++;
                    }
                }
            }
            carried += moved.premisesCarried();
        }
        assertTrue(asked > 1000, "too few rests were asked for this to hold anything: " + asked);
        assertTrue(carried > 1000, "too few premises were moved for this to hold anything: "
                + carried);
    }

    /**
     * A question is moved from the first work that kept it, and not from the first work that can be
     * moved over: a round with no room keeps none of what it was asked, and the work after it
     * still has the question.
     */
    @Test
    void aQuestionIsMovedFromTheWorkThatKeptItWhateverWorkIsBeforeIt() {
        Random dice = new Random(31671);
        long fromTheOneThatKeptIt = 0;
        long fromBoth = 0;
        for (int round = 0; round < CASES; round++) {
            CanonicalOrder<String> order = RulesNamingNoPositionInCommonCloseApartTest.ORDERS
                    .get(round % RulesNamingNoPositionInCommonCloseApartTest.ORDERS.size());
            List<AffineConstraint<String>> before = read(someRules(dice, 2 + dice.nextInt(4)));
            List<AffineConstraint<String>> after = new ArrayList<>(before);
            after.addAll(read(someRules(dice, 1 + dice.nextInt(2))));
            if (DifferenceBounds.over(before, order).holdsNothing()
                    || DifferenceBounds.over(after, order).holdsNothing()) {
                continue;
            }
            Box<String> start = someEnds(dice);
            Box<String> later = movedEnds(dice, start);

            RoundWork<String> kept = new RoundWork<>(before, start);
            askEveryRest(FormReach.over(before, start, DifferenceBounds.over(before, order), order)
                    .working(List.of(), kept), before, order);
            RoundWork<String> keptNone = new RoundWork<>(before, start, _ -> false);
            askEveryRest(FormReach.over(before, start, DifferenceBounds.over(before, order), order)
                    .working(List.of(), keptNone), before, order);

            fromTheOneThatKeptIt += carriedFrom(after, later, order, List.of(kept));
            fromBoth += carriedFrom(after, later, order, List.of(keptNone, kept));
        }
        assertTrue(fromTheOneThatKeptIt > 1000,
                "too few premises were moved for this to hold anything: " + fromTheOneThatKeptIt);
        assertEquals(fromTheOneThatKeptIt, fromBoth,
                "work that kept nothing stood before the work that kept the questions");
    }

    /** How many premises are moved when every rest and every form of {@code rules} is asked of a
     *  reading starting from {@code parents}. */
    private static long carriedFrom(List<AffineConstraint<String>> rules, Box<String> ends,
                                    CanonicalOrder<String> order, List<RoundWork<String>> parents) {
        FormReach<String> reading = FormReach.over(rules, ends,
                DifferenceBounds.over(rules, order), order)
                .working(parents, new RoundWork<>(rules, ends));
        askEveryRest(reading, rules, order);
        return reading.premisesCarried();
    }

    /** Every rest of every half-space, asked of a reading that keeps what it comes to. */
    private static void askEveryRest(FormReach<String> reading,
                                     List<AffineConstraint<String>> rules,
                                     CanonicalOrder<String> order) {
        for (AffineConstraint<String> rule : rules) {
            reading.ofKept(rule, rule.form().coefs());
            for (AffineConstraint.HalfSpace<String> half : rule.halfSpaces()) {
                FormReach<String>.Rests rests = reading.rests(rule, half);
                for (String atom : half.form().atomsIn(order)) {
                    rests.leastOfTheRest(atom);
                }
            }
        }
    }

    private static List<AffineConstraint<String>> read(List<Written> written) {
        return RulesAsWritten.statedOnly(written,
                RulesNamingNoPositionInCommonCloseApartTest::spacing);
    }

    private static List<Written> someRules(Random dice, int howMany) {
        List<Written> out = new ArrayList<>();
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
            ExactRatio constant = dice.nextInt(8) == 0
                    ? RulesNamingNoPositionInCommonCloseApartTest.A_HAIR
                    : ExactRatio.of(dice.nextInt(21) - 10);
            Rel[] all = Rel.values();
            out.add(new Written(coefs, constant, all[dice.nextInt(all.length)]));
        }
        return out;
    }

    private static Box<String> someEnds(Random dice) {
        Map<String, ExactCut> least = new LinkedHashMap<>();
        Map<String, ExactCut> most = new LinkedHashMap<>();
        for (String position : POSITIONS) {
            int low = dice.nextInt(15) - 10;
            int high = low + dice.nextInt(12);
            if (dice.nextInt(3) != 0) {
                least.put(position, cut(dice, low, high));
            }
            if (dice.nextInt(3) != 0) {
                most.put(position, cut(dice, high, low));
            }
        }
        return new Box<>(least, most);
    }

    /** {@code start} with the ends of none, one or several positions drawn again. */
    private static Box<String> movedEnds(Random dice, Box<String> start) {
        Map<String, ExactCut> least = new LinkedHashMap<>(start.atLeast());
        Map<String, ExactCut> most = new LinkedHashMap<>(start.atMost());
        int howMany = dice.nextInt(5) == 0 ? 2 + dice.nextInt(2) : dice.nextInt(2);
        for (int i = 0; i < howMany; i++) {
            String position = POSITIONS.get(dice.nextInt(POSITIONS.size()));
            int low = dice.nextInt(15) - 10;
            int high = low + dice.nextInt(12);
            switch (dice.nextInt(4)) {
                case 0 -> least.remove(position);
                case 1 -> most.remove(position);
                case 2 -> {
                    least.put(position, cut(dice, low, high));
                    most.put(position, cut(dice, high, low));
                }
                default -> {
                    ExactCut held = most.get(position);
                    if (held != null) {
                        most.put(position, held.inclusive()
                                ? ExactCut.exclusive(held.at()) : ExactCut.inclusive(held.at()));
                    }
                }
            }
        }
        return new Box<>(least, most);
    }

    private static ExactCut cut(Random dice, int at, int other) {
        return dice.nextBoolean() || at == other
                ? ExactCut.inclusive(ExactRatio.of(at)) : ExactCut.exclusive(ExactRatio.of(at));
    }
}
