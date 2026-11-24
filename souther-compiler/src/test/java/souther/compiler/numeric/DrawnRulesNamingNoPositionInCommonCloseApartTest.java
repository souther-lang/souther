package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.RulesAsWritten.Written;
import souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.Places;
import souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.Seen;
import souther.test.Nightly;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.A_HAIR;
import static souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.ONE_HALF;
import static souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.ORDERS;
import static souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.OTHER_HALF;
import static souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.aClosureLentItsPartsIsTheClosureInOneRun;
import static souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.aDomainLentItsPartsSaysWhatItSaysAlone;
import static souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.aHairApart;
import static souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.askFormsOverBothHalvesEitherWay;
import static souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.assertSomeFormWasBounded;
import static souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.boxed;
import static souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.halving;
import static souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.renamed;
import static souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.theClosureOfADealingIsTheProductOfTheClosureOfEach;

/**
 * Rules drawn at random that name no position in common leave together the product of what each of
 * them leaves.
 *
 * <p>The theorem is {@code RulesNamingNoPositionInCommonCloseApartTest}'s, and so are the claims
 * made of it, compared on the same outcome and counted over the same cases: the closure in one run
 * is the product of the halves closed apart, parted and kept a part at a time; a domain over both
 * halves answers forms over both alike either way; and rules said after a closure come to the same
 * state with its parts lent. What this adds is the halves: the ones there are written for the cases
 * the product has to carry, and these are drawn over three positions — bounds, differences, sums
 * weighted unevenly, now and then a rule over all three and a bound a hop cannot compose — then
 * renamed or drawn again for the other half, dealt into one list in an order drawn at every step,
 * and cut at a drawn place. That reaches halves and dealings no written half names. The seeds are
 * fixed, so a round that fails is the same round when it is run again.
 *
 * <p>A draw comes now and then to a rule that states no constraint. Every reader here is held to
 * another reader handed the same list, and none to the points, so such a rule is left out of both
 * ({@link RulesAsWritten#statedOnly}).
 *
 * <p>Nightly, for what it costs: every round closes the rules several times over. No cheaper way
 * asks whether a half or a dealing the written ones do not name breaks the theorem, and what it finds
 * is as well found by the morning as by the change that caused it, since the written halves stand in
 * the run every change waits on.
 */
@Nightly
class DrawnRulesNamingNoPositionInCommonCloseApartTest {

    private static final int CASES = 140;

    /** Fewer for the domain, which asks every form at every place under every relation. */
    private static final int DOMAINS = 20;

    @Test
    void theClosureOfBothHalvesIsTheProductOfTheClosureOfEach() {
        Random dice = new Random(2169);
        Seen seen = new Seen();
        for (int round = 0; round < CASES; round++) {
            CanonicalOrder<String> order = ORDERS.get(round % ORDERS.size());
            // Boxed every other time: a rule over three positions carries a bound from two of them
            // onto the third only where the two have ends, so without them a parting that left the
            // third out of the rule's part would answer the same and be checked for nothing.
            List<Written> drawn = someRules(dice, ONE_HALF);
            // Two of the three are enough to carry a bound onto the third.
            List<Written> one = dice.nextBoolean() ? boxed(drawn, List.of("a", "b")) : drawn;
            List<AffineConstraint<String>> left = read(one);
            List<AffineConstraint<String>> right = read(otherHalf(dice, round, one));
            theClosureOfADealingIsTheProductOfTheClosureOfEach(left, right,
                    dealt(dice, left, right), order, seen);
        }
        seen.coveredEveryCase();
    }

    @Test
    void aFormOverBothHalvesIsAnsweredAlikeEitherWay() {
        Random dice = new Random(1016);
        int bounded = 0;
        for (int round = 0; round < DOMAINS; round++) {
            List<Written> one = boxed(someRules(dice, ONE_HALF), ONE_HALF);
            List<Written> other = round % 2 == 0 ? renamed(one)
                    : boxed(someRules(dice, OTHER_HALF), OTHER_HALF);
            bounded += askFormsOverBothHalvesEitherWay(dealt(dice, one, other),
                    ORDERS.get(round % ORDERS.size()));
        }
        assertSomeFormWasBounded(bounded);
    }

    @Test
    void rulesSaidAfterAClosureComeToTheSameStateWithItsPartsLent() {
        Random dice = new Random(2481);
        Places places = new Places();
        for (int round = 0; round < CASES; round++) {
            CanonicalOrder<String> order = ORDERS.get(round % ORDERS.size());
            List<Written> one = dice.nextBoolean()
                    ? boxed(someRules(dice, ONE_HALF), List.of("a", "b")) : someRules(dice, ONE_HALF);
            List<Written> other = round % 2 == 0 ? renamed(one) : someRules(dice, OTHER_HALF);
            List<Written> written = dealt(dice, one, other);
            List<AffineConstraint<String>> both = read(written);
            aClosureLentItsPartsIsTheClosureInOneRun(both, dice.nextInt(both.size() + 1), order,
                    places);
            aDomainLentItsPartsSaysWhatItSaysAlone(written, order);
        }
        places.coveredEveryPlace("drawn");
    }

    /** The other half: now and then the halving pair, which the rounds run out on only after every
     *  round they have, and the hop nothing can compose, which a draw reaches only by luck; and
     *  otherwise the first half renamed or another half drawn. */
    private static List<Written> otherHalf(Random dice, int round, List<Written> one) {
        return round % 40 == 39 ? halving()
                : round % 10 == 4 ? aHairApart()
                : round % 2 == 0 ? renamed(one) : someRules(dice, OTHER_HALF);
    }

    /**
     * A handful of rules over {@code positions}: bounds, differences and sums weighted unevenly,
     * with now and then a bound a hop cannot compose onto a whole number.
     *
     * <p>Every other time, one of them weighs all three positions. A rule over three positions is
     * what joins a position to a part through no difference and no pair, so it is the case a
     * parting that took a rule for edges between two positions gets wrong, and it is drawn rather
     * than left to turn up. Not every time: rules over three positions that always hold one rule
     * over all of them are always one part, and a half whose rules fall apart is the product
     * taken inside the half.
     */
    private static List<Written> someRules(Random dice, List<String> positions) {
        List<Written> out = new ArrayList<>();
        if (dice.nextBoolean()) {
            Map<String, ExactRatio> overAll = new LinkedHashMap<>();
            for (String position : positions) {
                overAll.put(position, ExactRatio.of(dice.nextBoolean() ? 1 + dice.nextInt(2)
                        : -1 - dice.nextInt(2)));
            }
            out.add(new Written(overAll, ExactRatio.of(dice.nextInt(15) - 7),
                    dice.nextBoolean() ? Rel.LE : Rel.GE));
        }
        int howMany = 1 + dice.nextInt(3);
        for (int i = 0; i < howMany; i++) {
            Map<String, ExactRatio> coefs = new LinkedHashMap<>();
            for (String position : positions) {
                int weight = dice.nextInt(5) - 2;
                if (weight != 0) {
                    coefs.put(position, ExactRatio.of(weight));
                }
            }
            if (coefs.isEmpty()) {
                continue;
            }
            ExactRatio constant = dice.nextInt(8) == 0 ? A_HAIR : ExactRatio.of(dice.nextInt(15) - 7);
            Rel[] all = Rel.values();
            out.add(new Written(coefs, constant, all[dice.nextInt(all.length)]));
        }
        return out;
    }

    private static List<AffineConstraint<String>> read(List<Written> written) {
        return RulesAsWritten.statedOnly(written, RulesNamingNoPositionInCommonCloseApartTest::spacing);
    }

    /** Both lists in one, each kept in its own order, with which comes next drawn at every step. */
    private static <T> List<T> dealt(Random dice, List<T> one, List<T> other) {
        List<T> out = new ArrayList<>();
        int i = 0;
        int j = 0;
        while (i < one.size() || j < other.size()) {
            boolean fromOne = j >= other.size() || (i < one.size() && dice.nextBoolean());
            out.add(fromOne ? one.get(i++) : other.get(j++));
        }
        return out;
    }
}
