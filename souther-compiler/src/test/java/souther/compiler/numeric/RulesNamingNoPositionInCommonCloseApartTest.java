package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Rules that name no position in common leave together the product of what each of them leaves.
 *
 * <p>A theorem about the closure, and not about the table that keeps closures: the closure is
 * defined by every rule being read against every other in one run ({@link
 * ClosedState#closedTogether}), and what is held here is that parting the rules first and putting
 * the parts back together comes to that same state. {@link ClosedState} says why it does — the
 * differences never leave a part, a round narrows only the positions of the rule it reduces, and a
 * premise from another part tightens nothing while that part leaves its rule a value. A change to
 * how a premise or a round is read that breaks one of those breaks this.
 *
 * <p>The rules are drawn at random over three positions and then said again over three others, so
 * the two halves are independent by construction rather than by the luck of the draw, and the two
 * halves are dealt into one list in an order that is drawn too. The second half is the first under
 * other names as well as a second draw of its own: renamed, both halves ask the same thing and must
 * come to the same thing, and drawn apart, one half can hold nothing while the other holds plenty.
 * Now and then it is one of two systems written out instead, for the two cases a draw does not
 * reach: rules the rounds run out on, and a hop the exact arithmetic cannot compose.
 *
 * <p>Compared on everything a state answers and everything read off it afterwards. A domain is asked
 * about forms over positions of both halves once the closure is done, which no part asked about on
 * its own: those are answered out of the box and the differences of the whole, and a difference
 * between two halves is answered through nought from the bounds each half left.
 */
class RulesNamingNoPositionInCommonCloseApartTest {

    private static final List<String> ONE_HALF = List.of("a", "b", "cc");
    private static final List<String> OTHER_HALF = List.of("x", "y", "zz");
    private static final Map<String, String> RENAMED = Map.of("a", "x", "b", "y", "cc", "zz");

    /** Two positions over values that fill, for a pair of rules whose rounds never arrive. */
    private static final List<String> HALVING = List.of("p", "q");

    /** Two positions over values that fill, for a hop the exact arithmetic cannot compose. */
    private static final List<String> A_HAIR_APART = List.of("u", "v");

    private static final Function<String, Granularity> SPACING = position ->
            position.equals("b") || position.equals("y") || HALVING.contains(position)
                    || A_HAIR_APART.contains(position)
                    ? Granularity.DENSE : Granularity.DISCRETE;

    /**
     * A bound so far below one in scale that one plus it has no representation, so a hop from it
     * onto a whole number is a hop the exact arithmetic cannot compose.
     */
    private static final ExactRatio A_HAIR =
            ExactRatio.of(new BigDecimal(BigInteger.ONE, Integer.MAX_VALUE));

    private static final List<CanonicalOrder<String>> ORDERS = List.of(
            CanonicalOrder.asTheyAreSpelled(),
            (one, other) -> other.compareTo(one));

    private static final int CASES = 300;

    /** Fewer for the domain, which asks every form at every place under every relation. */
    private static final int DOMAINS = 30;

    @Test
    void theClosureOfBothHalvesIsTheProductOfTheClosureOfEach() {
        Random dice = new Random(2169);
        Seen seen = new Seen();
        for (int round = 0; round < CASES; round++) {
            CanonicalOrder<String> order = ORDERS.get(round % ORDERS.size());
            List<Written> one = someRules(dice, ONE_HALF);
            // The rounds run out on the halving pair only after every round they have, so it is
            // drawn now and then rather than as often as the others; and the hop nothing can
            // compose is said outright, since a draw reaches it only by luck.
            List<Written> other = switch (round % 10) {
                case 9 -> halving();
                case 4 -> aHairApart();
                default -> round % 2 == 0 ? renamed(one) : someRules(dice, OTHER_HALF);
            };
            List<AffineConstraint<String>> left = read(one);
            List<AffineConstraint<String>> right = read(other);
            List<AffineConstraint<String>> both = dealt(dice, left, right);

            Outcome inOneRun = outcome(ClosedState.closedTogether(both, SPACING, order));
            Outcome product = outcome(ClosedState.product(List.of(
                    ClosedState.closedTogether(left, SPACING, order),
                    ClosedState.closedTogether(right, SPACING, order))));
            Outcome parted = outcome(ClosedState.of(both, SPACING, order));
            Outcome kept = outcome(ClosedStates.kept().of(both, SPACING, order));

            assertEquals(inOneRun, product, () -> "the product of " + left + " and " + right
                    + " is not their closure in one run");
            assertEquals(inOneRun, parted, () -> both + " parted is not " + both + " in one run");
            assertEquals(inOneRun, kept, () -> both + " kept a part at a time is not " + both
                    + " in one run");
            seen.saw(inOneRun, outcome(ClosedState.closedTogether(left, SPACING, order)),
                    outcome(ClosedState.closedTogether(right, SPACING, order)));
        }
        seen.coveredEveryCase();
    }

    /**
     * And a domain over both halves answers forms over both alike, closed either way.
     *
     * <p>Asked through the domain because that is where a form over two halves is asked: after the
     * closure, out of what it handed back, and about positions no part asked about together.
     */
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

            // Parted through a kept table, which is the road a domain over many contexts takes; the
            // road that keeps nothing parts the rules the same way, and is held to the closure in
            // one run above.
            NumericDomain<String> inOneRun = said(both, order, ClosedStates.IN_ONE_RUN);
            NumericDomain<String> parted = said(both, order, ClosedStates.kept());
            assertEquals(inOneRun.isBottom(), parted.isBottom(), () -> both.toString());
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
            }
            for (String position : positionsOf(both)) {
                assertEquals(inOneRun.projectionOf(position), parted.projectionOf(position),
                        () -> "where " + position + " is under " + both);
            }
            for (Map<String, ExactRatio> form : formsOverBothHalves()) {
                if (!inOneRun.isBottom()
                        && inOneRun.projectionOf(new LinearForm<>(ExactRatio.ZERO, form))
                        instanceof NumericDomain.FormProjection.Within(NumericDomain.Bounds bounds)
                        && bounds.min() != null && bounds.max() != null) {
                    bounded++;
                }
            }
        }
        assertTrue(bounded > 0, "no form over both halves was bounded both ways, so the forms were"
                + " compared where they ran without end");
    }

    // --- what is compared -------------------------------------------------------------------------

    /**
     * Everything one state answers, as a value two states can be compared by.
     *
     * @param differences every difference between two positions of either half, both ways, and every
     *                    position's bounds as the differences have them
     * @param relations   the relations the differences hold, as a set: the order they are listed in
     *                    is the order the rules arrived in, which parting may change
     */
    private record Outcome(boolean holdsNothing, Box<String> box, ClosedState.Status status,
                           boolean everyBoundWasComposed, boolean differencesHoldNothing,
                           Map<String, ExactCut> differences,
                           Set<DifferenceBounds.Apart<String>> relations) {}

    private static Outcome outcome(ClosedState<String> closed) {
        DifferenceBounds<String> differences = closed.differences();
        if (closed.holdsNothing()) {
            return new Outcome(true, null, closed.status(), closed.everyBoundWasComposed(),
                    differences.holdsNothing(), null, null);
        }
        Map<String, ExactCut> apart = new LinkedHashMap<>();
        List<String> everywhere = new ArrayList<>(ONE_HALF);
        everywhere.addAll(OTHER_HALF);
        everywhere.addAll(HALVING);
        everywhere.addAll(A_HAIR_APART);
        for (String here : everywhere) {
            apart.put(here + " at most", differences.upperBoundOf(here));
            apart.put(here + " at least", differences.lowerBoundOf(here));
            for (String there : everywhere) {
                apart.put(here + " - " + there, differences.differenceBound(here, there));
            }
        }
        return new Outcome(false, closed.box(), closed.status(), closed.everyBoundWasComposed(),
                false, apart, new LinkedHashSet<>(differences.relations()));
    }

    /** Which of the cases the theorem is about the draws reached, so that a draw reaching none of
     *  them is not read as the theorem holding there. */
    private static final class Seen {
        int bothHoldSomething;
        int oneHoldsNothing;
        int ranOut;
        int notComposed;

        void saw(Outcome whole, Outcome left, Outcome right) {
            if (!left.holdsNothing() && !right.holdsNothing()) {
                bothHoldSomething++;
            }
            if (left.holdsNothing() != right.holdsNothing()) {
                oneHoldsNothing++;
            }
            if (!whole.holdsNothing() && whole.status() == ClosedState.Status.BUDGET_EXHAUSTED) {
                ranOut++;
            }
            if (!whole.holdsNothing() && !whole.everyBoundWasComposed()) {
                notComposed++;
            }
        }

        void coveredEveryCase() {
            String counts = bothHoldSomething + " where both halves hold something, "
                    + oneHoldsNothing + " where one of them holds nothing, " + ranOut
                    + " where the rounds ran out and " + notComposed
                    + " where a bound was not composed";
            assertTrue(bothHoldSomething > 0 && oneHoldsNothing > 0 && ranOut > 0
                    && notComposed > 0, "a case the theorem covers was never drawn: " + counts);
        }
    }

    // --- the rules --------------------------------------------------------------------------------

    private record Written(Map<String, ExactRatio> coefs, ExactRatio constant, Rel rel) {}

    /**
     * A handful of rules over {@code positions}: bounds, differences and sums weighted unevenly,
     * with now and then a bound a hop cannot compose onto a whole number.
     *
     * <p>One of them weighs all three positions, every time. A rule over three positions is what
     * joins a position to a part through no difference and no pair, so it is the case a parting
     * that took a rule for edges between two positions gets wrong, and it is drawn rather than
     * left to turn up.
     */
    private static List<Written> someRules(Random dice, List<String> positions) {
        List<Written> out = new ArrayList<>();
        Map<String, ExactRatio> overAll = new LinkedHashMap<>();
        for (String position : positions) {
            overAll.put(position, ExactRatio.of(dice.nextBoolean() ? 1 + dice.nextInt(2)
                    : -1 - dice.nextInt(2)));
        }
        out.add(new Written(overAll, ExactRatio.of(dice.nextInt(15) - 7),
                dice.nextBoolean() ? Rel.LE : Rel.GE));
        int howMany = dice.nextInt(5);
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

    /**
     * {@code rules} with each of {@code positions} held between minus nine and nine, so that a form
     * over both halves has ends to be read and not only no end on either side.
     */
    private static List<Written> boxed(List<Written> rules, List<String> positions) {
        List<Written> out = new ArrayList<>();
        for (String position : positions) {
            out.add(new Written(Map.of(position, ExactRatio.ONE), ExactRatio.of(9), Rel.GE));
            out.add(new Written(Map.of(position, ExactRatio.ONE), ExactRatio.of(-9), Rel.LE));
        }
        out.addAll(rules);
        return out;
    }

    /** The same rules over the other half's positions. */
    private static List<Written> renamed(List<Written> rules) {
        List<Written> out = new ArrayList<>();
        for (Written each : rules) {
            Map<String, ExactRatio> coefs = new LinkedHashMap<>();
            each.coefs().forEach((position, weight) -> coefs.put(RENAMED.get(position), weight));
            out.add(new Written(coefs, each.constant(), each.rel()));
        }
        return out;
    }

    /**
     * {@code 2p <= q} beside {@code 2q <= p} over values that fill, each held between nought and a
     * hundred: they descend by a quarter every round and never arrive, so the rounds run out.
     */
    private static List<Written> halving() {
        List<Written> out = new ArrayList<>();
        for (String position : HALVING) {
            out.add(new Written(Map.of(position, ExactRatio.ONE), ExactRatio.ZERO, Rel.GE));
            out.add(new Written(Map.of(position, ExactRatio.ONE), ExactRatio.of(-100), Rel.LE));
        }
        out.add(new Written(weighed("p", 2, "q", -1), ExactRatio.ZERO, Rel.LE));
        out.add(new Written(weighed("q", 2, "p", -1), ExactRatio.ZERO, Rel.LE));
        return out;
    }

    /**
     * {@code u - v <= A_HAIR} beside {@code v <= 1}: carrying the bound on {@code v} onto
     * {@code u} is one plus a hair, which the exact arithmetic has no representation for.
     */
    private static List<Written> aHairApart() {
        return List.of(
                new Written(weighed("u", 1, "v", -1), A_HAIR.negated(), Rel.LE),
                new Written(Map.of("v", ExactRatio.ONE), ExactRatio.ONE.negated(), Rel.LE));
    }

    private static Map<String, ExactRatio> weighed(String one, int itsWeight, String other,
                                                   int otherWeight) {
        Map<String, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(one, ExactRatio.of(itsWeight));
        coefs.put(other, ExactRatio.of(otherWeight));
        return coefs;
    }

    /** Forms over positions of both halves, of each shape a reading tells apart. */
    private static List<Map<String, ExactRatio>> formsOverBothHalves() {
        Map<String, ExactRatio> threeAcross = new LinkedHashMap<>();
        threeAcross.put("cc", ExactRatio.ONE);
        threeAcross.put("zz", ExactRatio.ONE);
        threeAcross.put("b", ExactRatio.ONE.negated());
        return List.of(weighed("a", 1, "x", 1), weighed("a", 1, "x", -1),
                weighed("a", 2, "y", -3), threeAcross);
    }

    private static List<AffineConstraint<String>> read(List<Written> written) {
        List<AffineConstraint<String>> out = new ArrayList<>();
        for (Written each : written) {
            if (AffineConstraint.of(each.coefs(), each.constant(), each.rel(), SPACING)
                    instanceof AffineConstraint.Read.Stated<String> stated) {
                out.add(stated.constraint());
            }
        }
        return out;
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

    private static NumericDomain<String> said(List<Written> rules, CanonicalOrder<String> order,
                                              ClosedStates closing) {
        Map<String, Granularity> kinds = new LinkedHashMap<>();
        List<String> everywhere = new ArrayList<>(ONE_HALF);
        everywhere.addAll(OTHER_HALF);
        everywhere.forEach(position -> kinds.put(position, SPACING.apply(position)));
        NumericDomain<String> out = NumericDomain.top(order, closing);
        for (Written each : rules) {
            out = out.assume(new LinearForm<>(each.constant(), each.coefs()), each.rel(), kinds);
        }
        return out;
    }

    private static Set<String> positionsOf(List<Written> rules) {
        Set<String> out = new LinkedHashSet<>();
        rules.forEach(each -> out.addAll(each.coefs().keySet()));
        return out;
    }
}
