package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.RulesAsWritten.Written;
import souther.compiler.numeric.RulesReaders.Orders;
import souther.compiler.numeric.RulesReaders.Reader;
import souther.compiler.numeric.RulesReaders.Tally;
import souther.test.Nightly;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static souther.compiler.numeric.RulesAsWritten.pointsSatisfying;
import static souther.compiler.numeric.RulesAsWritten.positionsOf;
import static souther.compiler.numeric.RulesAsWritten.someRuleHoldsNever;

/**
 * What every reader of a set of rules says is what the rules say, over rules drawn at random.
 *
 * <p>The claims and the readers are {@code EveryReaderOfRulesAnswersByTheRulesAloneTest}'s, and so
 * is the oracle, every point of a bounded range. What this adds is the systems: the chosen ones there
 * are written for the steps the readers take, and these are drawn from two shapes, rules over three
 * positions weighted from minus three to three at any threshold in the range with every relation, and
 * the bounds and differences the difference bounds are about, weighed by one or two, strict or not.
 * A combination no chosen system names is one a draw can reach. The seeds are fixed, so a round that
 * fails is the same round when it is run again.
 *
 * <p>A draw of the first shape comes now and then to a rule no value satisfies, a weighted equality
 * whose threshold the weights cannot reach. There is no constraint to hand on for it, and what is owed
 * instead is that the points hold nothing either, which is asked before the round is passed over.
 *
 * <p>Nightly, for what it costs: hundreds of draws for each of three readers, each enumerated over the
 * whole range. No cheaper way asks whether a step the chosen systems do not name goes wrong somewhere
 * among the combinations, and what it finds is as well found by the morning as by the change that
 * caused it, since the chosen systems stand in the run every change waits on.
 */
@Nightly
class EveryReaderOfDrawnRulesAnswersByTheRulesAloneTest {

    private static final List<String> POSITIONS = List.of("a", "b", "c");
    private static final int CASES = 150;

    /** A way of drawing a system, and the seed it is drawn from. */
    private record Shape(String name, Function<Random, List<Written>> draw) {
    }

    private static final List<Shape> SHAPES = List.of(
            new Shape("weighted rules over three positions",
                    EveryReaderOfDrawnRulesAnswersByTheRulesAloneTest::someRules),
            new Shape("bounds and differences",
                    EveryReaderOfDrawnRulesAnswersByTheRulesAloneTest::someDifferences));

    /** A few orders of the rules, which for rules drawn at random is as many as are worth asking. */
    private static Orders shuffles(Random dice) {
        return system -> {
            List<List<Written>> out = new ArrayList<>();
            for (int i = 0; i < 3; i++) {
                List<Written> shuffled = new ArrayList<>(system);
                Collections.shuffle(shuffled, dice);
                out.add(shuffled);
            }
            return out;
        };
    }

    @Test
    void theOrderTheRulesArrivedInIsNotPartOfTheAnswer() {
        for (Shape shape : SHAPES) {
            for (Reader reader : RulesReaders.READERS) {
                Random dice = new Random(16);
                for (int round = 0; round < CASES; round++) {
                    List<Written> system = shape.draw().apply(dice);
                    if (heldNowhere(system)) {
                        continue;
                    }
                    RulesReaders.theOrderTheRulesArrivedInIsNotPartOfTheAnswer(reader, system,
                            shuffles(dice));
                }
            }
        }
    }

    @Test
    void sayingARuleTwiceSaysWhatSayingItOnceSays() {
        for (Shape shape : SHAPES) {
            for (Reader reader : RulesReaders.READERS) {
                Random dice = new Random(1016);
                for (int round = 0; round < CASES; round++) {
                    List<Written> system = shape.draw().apply(dice);
                    if (heldNowhere(system)) {
                        continue;
                    }
                    RulesReaders.sayingARuleTwiceSaysWhatSayingItOnceSays(reader, system);
                }
            }
        }
    }

    @Test
    void noPointTheRulesAdmitIsEverRefused() {
        for (Shape shape : SHAPES) {
            for (Reader reader : RulesReaders.READERS) {
                Random dice = new Random(4800);
                Tally tally = new Tally();
                for (int round = 0; round < CASES; round++) {
                    List<Written> system = shape.draw().apply(dice);
                    if (heldNowhere(system)) {
                        continue;
                    }
                    RulesReaders.noPointTheRulesAdmitIsRefused(reader, system, tally);
                }
                RulesReaders.assertBothWaysWereChecked(reader, tally, CASES / 10);
            }
        }
    }

    /** Whether a drawn rule holds at no value, in which case the points must hold nothing too and
     *  there is nothing to hand on. */
    private static boolean heldNowhere(List<Written> system) {
        if (!someRuleHoldsNever(system, atom -> Granularity.DISCRETE)) {
            return false;
        }
        assertEquals(List.of(),
                pointsSatisfying(system, List.copyOf(positionsOf(system)), RulesReaders.LOW,
                        RulesReaders.HIGH),
                () -> "a rule of " + system + " was read as holding nowhere, and points satisfy it");
        return true;
    }

    private static Rel someRelation(Random dice) {
        // taken from the enum, so that a relation added to the language is drawn here without
        // anyone remembering to add it
        Rel[] all = Rel.values();
        return all[dice.nextInt(all.length)];
    }

    /** One to three rules over the three positions, weighted unevenly, which is what the difference
     *  bounds cannot hold and what the reduction exists for. */
    private static List<Written> someRules(Random dice) {
        List<Written> out = new ArrayList<>();
        int howMany = 1 + dice.nextInt(3);
        for (int i = 0; i < howMany; i++) {
            Map<String, ExactRatio> coefs = new LinkedHashMap<>();
            for (String position : POSITIONS) {
                int weight = dice.nextInt(7) - 3;
                if (weight != 0) {
                    coefs.put(position, ExactRatio.of(weight));
                }
            }
            if (coefs.isEmpty()) {
                continue;
            }
            out.add(new Written(coefs, ExactRatio.of(dice.nextInt(21) - 10L), someRelation(dice)));
        }
        return out;
    }

    /** Two to five rules of the shapes the difference bounds have: a bound on one position, or a
     *  difference of two. */
    private static List<Written> someDifferences(Random dice) {
        List<Written> out = new ArrayList<>();
        int howMany = 2 + dice.nextInt(4);
        for (int i = 0; i < howMany; i++) {
            String one = POSITIONS.get(dice.nextInt(POSITIONS.size()));
            long threshold = RulesReaders.LOW
                    + (long) dice.nextInt(RulesReaders.HIGH - RulesReaders.LOW + 1);
            boolean strict = dice.nextBoolean();
            // A weight of two as often as one, so the shape canonicalisation brought in is
            // exercised rather than assumed.
            long weight = dice.nextBoolean() ? 1 : 2;
            if (dice.nextBoolean()) {
                Rel rel = dice.nextBoolean()
                        ? (strict ? Rel.LT : Rel.LE) : (strict ? Rel.GT : Rel.GE);
                out.add(new Written(Map.of(one, ExactRatio.of(weight)),
                        ExactRatio.of(-threshold * weight), rel));
            } else {
                String other = POSITIONS.get(dice.nextInt(POSITIONS.size()));
                if (one.equals(other)) {
                    continue;
                }
                Map<String, ExactRatio> coefs = new LinkedHashMap<>();
                coefs.put(one, ExactRatio.of(weight));
                coefs.put(other, ExactRatio.of(-weight));
                out.add(new Written(coefs, ExactRatio.of(-threshold * weight),
                        strict ? Rel.LT : Rel.LE));
            }
        }
        return out;
    }
}
