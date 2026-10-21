package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.RulesAsWritten.Written;
import souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.Outcome;
import souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.Seen;
import souther.test.Nightly;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static souther.compiler.numeric.RulesAsWritten.positionsOf;
import static souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.A_HAIR;
import static souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.ONE_HALF;
import static souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.ORDERS;
import static souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.OTHER_HALF;
import static souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.aHairApart;
import static souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.boxed;
import static souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.formsOverBothHalves;
import static souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.halving;
import static souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.outcome;
import static souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.renamed;
import static souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.said;
import static souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.saidAskingOnTheWay;

/**
 * Rules drawn at random that name no position in common leave together the product of what each of
 * them leaves.
 *
 * <p>The theorem is {@code RulesNamingNoPositionInCommonCloseApartTest}'s, compared on the same
 * outcome and counted over the same cases: the closure in one run is the product of the halves
 * closed apart, parted and kept a part at a time; a domain over both halves answers forms over both
 * alike either way; and rules said after a closure come to the same state with its parts lent. What
 * this adds is the halves: the ones there are written for the cases the product has to carry, and
 * these are drawn over three positions — bounds, differences, sums weighted unevenly, now and then a
 * rule over all three and a bound a hop cannot compose — then renamed or drawn again for the other
 * half, dealt into one list in an order drawn at every step, and cut at a drawn place. That reaches
 * halves and dealings no written half names. The seeds are fixed, so a round that fails is the same
 * round when it is run again.
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
            // The rounds run out on the halving pair only after every round they have, so it is
            // drawn now and then rather than as often as the others; and the hop nothing can
            // compose is said outright, since a draw reaches it only by luck.
            List<Written> other = round % 40 == 39 ? halving()
                    : round % 10 == 4 ? aHairApart()
                    : round % 2 == 0 ? renamed(one) : someRules(dice, OTHER_HALF);
            List<AffineConstraint<String>> left = read(one);
            List<AffineConstraint<String>> right = read(other);
            List<AffineConstraint<String>> both = dealt(dice, left, right);

            ClosedState<String> leftClosed = ClosedState.closedTogether(left,
                    RulesNamingNoPositionInCommonCloseApartTest::spacing, order);
            ClosedState<String> rightClosed = ClosedState.closedTogether(right,
                    RulesNamingNoPositionInCommonCloseApartTest::spacing, order);
            Outcome inOneRun = outcome(ClosedState.closedTogether(both,
                    RulesNamingNoPositionInCommonCloseApartTest::spacing, order));
            Outcome product = outcome(ClosedState.product(List.of(leftClosed, rightClosed)));
            Outcome parted = outcome(ClosedState.of(both,
                    RulesNamingNoPositionInCommonCloseApartTest::spacing, order));
            Outcome kept = outcome(ClosedStates.kept().of(both,
                    RulesNamingNoPositionInCommonCloseApartTest::spacing, order));

            assertEquals(inOneRun, product, () -> "the product of " + left + " and " + right
                    + " is not their closure in one run");
            assertEquals(inOneRun, parted, () -> both + " parted is not " + both + " in one run");
            assertEquals(inOneRun, kept, () -> both + " kept a part at a time is not " + both
                    + " in one run");
            seen.saw(inOneRun, leftClosed.holdsNothing(), rightClosed.holdsNothing(),
                    ClosureQuestion.independentRules(both).size());
        }
        seen.coveredEveryCase();
    }

    /** And a domain over both halves answers forms over both alike, closed either way. */
    @Test
    void aFormOverBothHalvesIsAnsweredAlikeEitherWay() {
        Random dice = new Random(1016);
        int bounded = 0;
        for (int round = 0; round < DOMAINS; round++) {
            CanonicalOrder<String> order = ORDERS.get(round % ORDERS.size());
            List<Written> one = boxed(someRules(dice, ONE_HALF), ONE_HALF);
            List<Written> other = round % 2 == 0 ? renamed(one)
                    : boxed(someRules(dice, OTHER_HALF), OTHER_HALF);
            List<Written> both = dealt(dice, one, other);

            NumericDomain<String> inOneRun = said(both, order, ClosedStates.IN_ONE_RUN);
            NumericDomain<String> parted = said(both, order, ClosedStates.kept());
            assertEquals(inOneRun.isBottom(), parted.isBottom(), both::toString);
            for (Map<String, ExactRatio> form : formsOverBothHalves()) {
                LinearForm<String> asked = new LinearForm<>(ExactRatio.ZERO, form);
                assertEquals(inOneRun.projectionOf(asked), parted.projectionOf(asked),
                        () -> "what " + form + " runs between under " + both);
                for (int at = -4; at <= 4; at += 4) {
                    LinearForm<String> shifted = new LinearForm<>(ExactRatio.of(at), form);
                    for (Rel rel : List.of(Rel.LE, Rel.LT, Rel.GE, Rel.EQ)) {
                        assertEquals(inOneRun.entails(shifted, rel), parted.entails(shifted, rel),
                                () -> "whether " + shifted + " " + rel + " 0 follows from " + both);
                        assertEquals(inOneRun.refutes(shifted, rel), parted.refutes(shifted, rel),
                                () -> "whether " + shifted + " " + rel + " 0 is refused by "
                                        + both);
                    }
                }
                if (!inOneRun.isBottom()
                        && inOneRun.projectionOf(asked)
                        instanceof NumericDomain.FormProjection.Within(NumericDomain.Bounds bounds)
                        && bounds.min() != null && bounds.max() != null) {
                    bounded++;
                }
            }
            for (String position : positionsOf(both)) {
                assertEquals(inOneRun.projectionOf(position), parted.projectionOf(position),
                        () -> "where " + position + " is under " + both);
            }
        }
        assertTrue(bounded > 0, "no form over both halves was bounded both ways, so the forms were"
                + " compared where they ran without end");
    }

    /** And rules said after a closure was worked out come to the same state with that closure's
     *  parts lent as without, cut at a drawn place. */
    @Test
    void rulesSaidAfterAClosureComeToTheSameStateWithItsPartsLent() {
        Random dice = new Random(2481);
        int joinedOne = 0;
        int stoodApart = 0;
        int joinedTwo = 0;
        for (int round = 0; round < CASES; round++) {
            CanonicalOrder<String> order = ORDERS.get(round % ORDERS.size());
            List<Written> one = dice.nextBoolean()
                    ? boxed(someRules(dice, ONE_HALF), List.of("a", "b")) : someRules(dice, ONE_HALF);
            List<Written> other = round % 2 == 0 ? renamed(one) : someRules(dice, OTHER_HALF);
            List<Written> written = dealt(dice, one, other);
            List<AffineConstraint<String>> both = read(written);
            int cut = dice.nextInt(both.size() + 1);
            List<AffineConstraint<String>> first = both.subList(0, cut);

            ClosedStates kept = ClosedStates.kept();
            ClosedStates.Parted<String> before = kept.of(first,
                    RulesNamingNoPositionInCommonCloseApartTest::spacing, order, null);
            long askedBefore = kept.questionsAsked();
            ClosedStates.Parted<String> after = kept.of(both,
                    RulesNamingNoPositionInCommonCloseApartTest::spacing, order, before);
            long asked = kept.questionsAsked() - askedBefore;
            Outcome inOneRun = outcome(ClosedState.closedTogether(both,
                    RulesNamingNoPositionInCommonCloseApartTest::spacing, order));

            assertEquals(inOneRun, outcome(after.state()), () -> both + " lent the parts of "
                    + first + " is not " + both + " in one run");
            NumericDomain<String> alone = said(written, order, ClosedStates.IN_ONE_RUN);
            NumericDomain<String> lent = saidAskingOnTheWay(written, order);
            assertEquals(alone.isBottom(), lent.isBottom(), written::toString);
            for (String position : positionsOf(written)) {
                assertEquals(alone.projectionOf(position), lent.projectionOf(position),
                        () -> "where " + position + " is under " + written);
            }

            // Where each later rule goes, taken in the order they were said, so that a later rule
            // meets the parts the ones before it made. Only the parts they reach are asked about,
            // unless one of them joins two, and then every part of all the rules is.
            Map<String, Integer> partOf = new LinkedHashMap<>();
            List<List<AffineConstraint<String>>> parts = ClosureQuestion.independentRules(first);
            for (int at = 0; at < parts.size(); at++) {
                for (AffineConstraint<String> rule : parts.get(at)) {
                    for (String position : rule.form().coefs().keySet()) {
                        partOf.put(position, at);
                    }
                }
            }
            int made = parts.size();
            Set<Integer> reachedAtAll = new LinkedHashSet<>();
            boolean joined = false;
            for (AffineConstraint<String> later : both.subList(cut, both.size())) {
                Set<Integer> reached = new LinkedHashSet<>();
                later.form().coefs().keySet().forEach(position -> {
                    if (partOf.containsKey(position)) {
                        reached.add(partOf.get(position));
                    }
                });
                if (reached.size() > 1) {
                    joinedTwo++;
                    joined = true;
                    break;
                }
                int part;
                if (reached.isEmpty()) {
                    stoodApart++;
                    part = made++;
                } else {
                    joinedOne++;
                    part = reached.iterator().next();
                }
                reachedAtAll.add(part);
                for (String position : later.form().coefs().keySet()) {
                    partOf.put(position, part);
                }
            }
            long expected = joined ? ClosureQuestion.independentRules(both).size()
                    : reachedAtAll.size();
            assertEquals(expected, asked, () -> "the questions put once " + first
                    + " was lent to " + both);
        }
        int ones = joinedOne;
        int aparts = stoodApart;
        int twos = joinedTwo;
        assertTrue(joinedOne > 0 && stoodApart > 0 && joinedTwo > 0, () -> "a place a later rule"
                + " can go was never drawn: " + ones + " joined one part, " + aparts
                + " stood apart and " + twos + " joined two");
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
