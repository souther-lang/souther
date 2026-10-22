package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.RulesAsWritten.Written;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static souther.compiler.numeric.RulesAsWritten.eachWholeAtEveryPlace;
import static souther.compiler.numeric.RulesAsWritten.inTurn;
import static souther.compiler.numeric.RulesAsWritten.positionsOf;
import static souther.compiler.numeric.RulesAsWritten.rules;

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
 * <p>The rules are written over three positions ({@link #HALVES}) and then said again over three
 * others, so the two halves are independent by construction, and the two halves are dealt into one
 * list each in its own order: either half whole at every place among the other's rules, and the two
 * taken in turn ({@link RulesAsWritten#eachWholeAtEveryPlace}). Parting puts a part's rules in the
 * order they came, so those are the orders a parting that read a rule's place in the list rather
 * than its positions would answer differently in. The second half is the first under other names as
 * well as another half of its own: renamed, both halves ask the same thing and must come to the
 * same thing, and written apart, one half can hold nothing while the other holds plenty. Each half
 * is written for a case the product has to carry: a rule over three positions that joins the third
 * through no difference, a weighted sum beside a difference, a half holding nothing, and a half that
 * falls into parts of its own. Two systems are written out besides, for the two cases no half of
 * whole numbers reaches: rules the rounds run out on, and a hop the exact arithmetic cannot compose.
 *
 * <p>Compared on everything a state answers and everything read off it afterwards. A domain is asked
 * about forms over positions of both halves once the closure is done, which no part asked about on
 * its own: those are answered out of the box and the differences of the whole, and a difference
 * between two halves is answered through nought from the bounds each half left.
 */
class RulesNamingNoPositionInCommonCloseApartTest {

    static final List<String> ONE_HALF = List.of("a", "b", "cc");
    static final List<String> OTHER_HALF = List.of("x", "y", "zz");
    private static final Map<String, String> RENAMED = Map.of("a", "x", "b", "y", "cc", "zz");

    /** Two positions over values that fill, for a pair of rules whose rounds never arrive. */
    private static final List<String> HALVING = List.of("p", "q");

    /** Two positions over values that fill, for a hop the exact arithmetic cannot compose. */
    private static final List<String> A_HAIR_APART = List.of("u", "v");

    /**
     * Whole numbers for the written halves, and values that fill for the two systems written out.
     *
     * <p>A half is often boxed, and over whole numbers in a box the rounds stop on their own, each
     * taking some end a whole step in. Over values that fill, a box and a sum weighted unevenly
     * descend through fractions until the rounds run out, which is the halving pair's case.
     */
    static Granularity spacing(String position) {
        return HALVING.contains(position) || A_HAIR_APART.contains(position)
                ? Granularity.DENSE : Granularity.DISCRETE;
    }

    /**
     * A bound so far below one in scale that one plus it has no representation, so a hop from it
     * onto a whole number is a hop the exact arithmetic cannot compose.
     */
    static final ExactRatio A_HAIR =
            ExactRatio.of(new BigDecimal(BigInteger.ONE, Integer.MAX_VALUE));

    static final List<CanonicalOrder<String>> ORDERS = List.of(
            CanonicalOrder.asTheyAreSpelled(),
            (one, other) -> other.compareTo(one));

    /**
     * Halves over {@link #ONE_HALF}, each with what it is for.
     *
     * <p>Where a and b are boxed it is because a rule over three positions carries a bound from two
     * of them onto the third only where the two have ends, so without them a parting that left the
     * third out of the rule's part would answer the same and be checked for nothing.
     */
    private static final List<List<Written>> HALVES = List.of(
            // A rule over all three positions, which joins cc to a and b through no difference, and
            // a later bound on a tighter than its box.
            boxed(rules("a + b - 2cc <= 1", "a - b <= 2", "a <= 2"), List.of("a", "b")),
            // A weighted sum beside a difference.
            rules("2a - b >= 1", "b - cc <= 0", "cc <= 3"),
            // A half holding nothing.
            boxed(rules("a + b >= 9"), List.of("a", "b")),
            // A half that falls into parts of its own: a hole sided by a bound, and a sum on its own.
            rules("a /= 0", "a >= 0", "-cc - b < 2", "cc <= 3"));

    /** Which half goes beside which: renamed, written apart, and the two systems written out. */
    private static List<List<List<Written>>> pairs() {
        List<Written> carrying = HALVES.get(0);
        List<Written> weighted = HALVES.get(1);
        List<Written> empty = HALVES.get(2);
        List<Written> inParts = HALVES.get(3);
        return List.of(
                List.of(carrying, renamed(carrying)),
                List.of(weighted, renamed(weighted)),
                List.of(inParts, renamed(inParts)),
                List.of(carrying, renamed(empty)),
                List.of(empty, renamed(weighted)),
                List.of(inParts, renamed(carrying)),
                List.of(weighted, halving()),
                List.of(carrying, aHairApart()));
    }

    /** The pairs whose second half is over {@link #OTHER_HALF}, which a domain over the two halves
     *  is asked about. */
    private static List<List<List<Written>>> twoHalves() {
        List<List<List<Written>>> out = new ArrayList<>();
        for (List<List<Written>> pair : pairs()) {
            if (OTHER_HALF.containsAll(positionsOf(pair.get(1)))) {
                out.add(pair);
            }
        }
        return out;
    }

    @Test
    void theClosureOfBothHalvesIsTheProductOfTheClosureOfEach() {
        Seen seen = new Seen();
        for (List<List<Written>> pair : pairs()) {
            List<AffineConstraint<String>> left = read(pair.get(0));
            List<AffineConstraint<String>> right = read(pair.get(1));
            for (CanonicalOrder<String> order : ORDERS) {
                ClosedState<String> leftClosed = ClosedState.closedTogether(left,
                        RulesNamingNoPositionInCommonCloseApartTest::spacing, order);
                ClosedState<String> rightClosed = ClosedState.closedTogether(right,
                        RulesNamingNoPositionInCommonCloseApartTest::spacing, order);
                Outcome product = outcome(ClosedState.product(List.of(leftClosed, rightClosed)));
                for (List<AffineConstraint<String>> both : eachWholeAtEveryPlace(left, right)) {
                    Outcome inOneRun = outcome(ClosedState.closedTogether(both,
                            RulesNamingNoPositionInCommonCloseApartTest::spacing, order));
                    Outcome parted = outcome(ClosedState.of(both,
                            RulesNamingNoPositionInCommonCloseApartTest::spacing, order));
                    Outcome kept = outcome(ClosedStates.kept().of(both,
                            RulesNamingNoPositionInCommonCloseApartTest::spacing, order));

                    assertEquals(inOneRun, product, () -> "the product of " + left + " and "
                            + right + " is not their closure in one run");
                    assertEquals(inOneRun, parted,
                            () -> both + " parted is not " + both + " in one run");
                    assertEquals(inOneRun, kept, () -> both + " kept a part at a time is not "
                            + both + " in one run");
                    seen.saw(inOneRun, leftClosed.holdsNothing(), rightClosed.holdsNothing(),
                            ClosureQuestion.independentRules(both).size());
                }
            }
        }
        seen.coveredEveryCase();
    }

    /**
     * And a domain over both halves answers forms over both alike, closed either way.
     *
     * <p>Asked through the domain because that is where a form over two halves is asked: after the
     * closure, out of what it handed back, and about positions no part asked about together. Every
     * position is boxed, so a form over both halves has ends to be read and not only no end on
     * either side.
     */
    @Test
    void aFormOverBothHalvesIsAnsweredAlikeEitherWay() {
        int bounded = 0;
        int each = 0;
        for (List<List<Written>> pair : twoHalves()) {
            List<Written> one = boxed(pair.get(0), ONE_HALF);
            List<Written> other = boxed(pair.get(1), OTHER_HALF);
            List<Written> both = inTurn(one, other);
            CanonicalOrder<String> order = ORDERS.get(each++ % ORDERS.size());
            // Parted through a kept table, which is the road a domain over many contexts takes; the
            // road that keeps nothing parts the rules the same way, and is held to the closure in
            // one run above.
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
                                () -> "whether " + shifted + " " + rel + " 0 follows from "
                                        + both);
                        assertEquals(inOneRun.refutes(shifted, rel), parted.refutes(shifted, rel),
                                () -> "whether " + shifted + " " + rel + " 0 is refused by "
                                        + both);
                    }
                }
                if (inOneRun.projectionOf(asked)
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

    /**
     * And rules said after a closure was worked out come to the same state with that closure's parts
     * lent as without.
     *
     * <p>What lending does is decide where each rule said later goes among the parts the closure
     * before it had: at the end of the one part whose positions it weighs, into a part of its own
     * after all of them, or — where it weighs positions of two — nowhere, with the parts worked out
     * from the rules. What the table lends is the parts of the rules said before the cut, so the
     * rules are cut after every count of each half's own: the first {@code i} of one half and the
     * first {@code j} of the other said first, taken in turn, and the rest after. Each of the three
     * places is reached, and each is counted. A domain is lent whatever the one it was made from had
     * worked out by then, so the rules are said into one at a time with what they leave asked after
     * every rule on the way, which cuts every order they are said in at every place; the orders are
     * the halves dealt as {@link RulesAsWritten#eachWholeAtEveryPlace} deals them.
     */
    @Test
    void rulesSaidAfterAClosureComeToTheSameStateWithItsPartsLent() {
        int joinedOne = 0;
        int stoodApart = 0;
        int joinedTwo = 0;
        int each = 0;
        for (List<List<Written>> pair : twoHalves()) {
            List<Written> one = pair.get(0);
            List<Written> other = pair.get(1);
            for (List<Written> written : eachWholeAtEveryPlace(one, other)) {
                CanonicalOrder<String> order = ORDERS.get(each++ % ORDERS.size());
                NumericDomain<String> alone = said(written, order, ClosedStates.IN_ONE_RUN);
                NumericDomain<String> lent = saidAskingOnTheWay(written, order);
                assertEquals(alone.isBottom(), lent.isBottom(), written::toString);
                for (String position : positionsOf(written)) {
                    assertEquals(alone.projectionOf(position), lent.projectionOf(position),
                            () -> "where " + position + " is under " + written);
                }
            }
            for (int ofOne = 0; ofOne <= one.size(); ofOne++) {
                for (int ofOther = 0; ofOther <= other.size(); ofOther++) {
                    List<Written> written = new ArrayList<>(
                            inTurn(one.subList(0, ofOne), other.subList(0, ofOther)));
                    int cut = read(written).size();
                    written.addAll(inTurn(one.subList(ofOne, one.size()),
                            other.subList(ofOther, other.size())));
                    CanonicalOrder<String> order = ORDERS.get(each++ % ORDERS.size());
                    List<AffineConstraint<String>> both = read(written);
                    Outcome inOneRun = outcome(ClosedState.closedTogether(both,
                            RulesNamingNoPositionInCommonCloseApartTest::spacing, order));
                    List<AffineConstraint<String>> first = both.subList(0, cut);
                    ClosedStates kept = ClosedStates.kept();
                    ClosedStates.Parted<String> before = kept.of(first,
                            RulesNamingNoPositionInCommonCloseApartTest::spacing, order, null);
                    long askedBefore = kept.questionsAsked();
                    ClosedStates.Parted<String> after = kept.of(both,
                            RulesNamingNoPositionInCommonCloseApartTest::spacing, order, before);
                    long asked = kept.questionsAsked() - askedBefore;

                    assertEquals(inOneRun, outcome(after.state()), () -> both + " lent the parts of "
                            + first + " is not " + both + " in one run");

                    // Where each later rule goes, taken in the order they were said, so that a later
                    // rule meets the parts the ones before it made. Only the parts they reach are
                    // asked about, unless one of them joins two, and then every part of all the
                    // rules is.
                    Map<String, Integer> partOf = new LinkedHashMap<>();
                    List<List<AffineConstraint<String>>> parts =
                            ClosureQuestion.independentRules(first);
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
            }
        }
        int ones = joinedOne;
        int aparts = stoodApart;
        int twos = joinedTwo;
        assertTrue(joinedOne > 0 && stoodApart > 0 && joinedTwo > 0, () -> "a place a later rule"
                + " can go was never reached: " + ones + " joined one part, " + aparts
                + " stood apart and " + twos + " joined two");
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
    record Outcome(boolean holdsNothing, Box<String> box, ClosedState.Status status,
                           boolean everyBoundWasComposed, boolean differencesHoldNothing,
                           Map<String, ExactCut> differences,
                           Set<DifferenceBounds.Apart<String>> relations) {}

    static Outcome outcome(ClosedState<String> closed) {
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

    /** Which of the cases the theorem is about the halves reached, so that a list reaching none of
     *  them is not read as the theorem holding there. */
    static final class Seen {
        int bothHoldSomething;
        int oneHoldsNothing;
        int ranOut;
        int notComposed;
        int aHalfInParts;

        void saw(Outcome whole, boolean leftHoldsNothing, boolean rightHoldsNothing, int parts) {
            // More parts than the two halves: a half whose own rules fall apart, which is the
            // product taken inside a half as well as across the two.
            if (parts > 2) {
                aHalfInParts++;
            }
            if (!leftHoldsNothing && !rightHoldsNothing) {
                bothHoldSomething++;
            }
            if (leftHoldsNothing != rightHoldsNothing) {
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
                    + " where a bound was not composed, and " + aHalfInParts
                    + " where a half fell apart on its own";
            assertTrue(bothHoldSomething > 0 && oneHoldsNothing > 0 && ranOut > 0
                    && notComposed > 0 && aHalfInParts > 0,
                    "a case the theorem covers was never reached: " + counts);
        }
    }

    // --- the rules --------------------------------------------------------------------------------

    /** {@code rules} with each of {@code positions} held between minus four and four. */
    static List<Written> boxed(List<Written> rules, List<String> positions) {
        return RulesAsWritten.boxed(rules, positions, -4, 4);
    }

    /** The same rules over the other half's positions. */
    static List<Written> renamed(List<Written> rules) {
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
    static List<Written> halving() {
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
    static List<Written> aHairApart() {
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
    static List<Map<String, ExactRatio>> formsOverBothHalves() {
        Map<String, ExactRatio> threeAcross = new LinkedHashMap<>();
        threeAcross.put("cc", ExactRatio.ONE);
        threeAcross.put("zz", ExactRatio.ONE);
        threeAcross.put("b", ExactRatio.ONE.negated());
        return List.of(weighed("a", 1, "x", 1), weighed("a", 1, "x", -1),
                weighed("a", 2, "y", -3), threeAcross);
    }

    private static List<AffineConstraint<String>> read(List<Written> written) {
        return RulesAsWritten.read(written, RulesNamingNoPositionInCommonCloseApartTest::spacing);
    }

    static NumericDomain<String> said(List<Written> rules, CanonicalOrder<String> order,
                                              ClosedStates closing) {
        Map<String, Granularity> kinds = kinds(rules);
        NumericDomain<String> out = NumericDomain.top(order, closing);
        for (Written each : rules) {
            out = out.assume(new LinearForm<>(each.constant(), each.coefs()), each.rel(), kinds);
        }
        return out;
    }

    private static Map<String, Granularity> kinds(List<Written> rules) {
        Map<String, Granularity> kinds = new LinkedHashMap<>();
        List<String> everywhere = new ArrayList<>(ONE_HALF);
        everywhere.addAll(OTHER_HALF);
        everywhere.addAll(positionsOf(rules));
        everywhere.forEach(position -> kinds.put(position, spacing(position)));
        return kinds;
    }

    /**
     * {@link #said} through a kept table, asking whether anything is left after every rule, so that
     * each domain is lent what the one before it had worked out by then — and each answer on the way
     * held to the same rules closed in one run.
     */
    static NumericDomain<String> saidAskingOnTheWay(List<Written> rules,
                                                            CanonicalOrder<String> order) {
        Map<String, Granularity> kinds = kinds(rules);
        NumericDomain<String> out = NumericDomain.top(order, ClosedStates.kept());
        NumericDomain<String> alone = NumericDomain.top(order, ClosedStates.IN_ONE_RUN);
        for (Written each : rules) {
            LinearForm<String> said = new LinearForm<>(each.constant(), each.coefs());
            out = out.assume(said, each.rel(), kinds);
            alone = alone.assume(said, each.rel(), kinds);
            assertEquals(alone.isBottom(), out.isBottom(), rules::toString);
        }
        return out;
    }
}
