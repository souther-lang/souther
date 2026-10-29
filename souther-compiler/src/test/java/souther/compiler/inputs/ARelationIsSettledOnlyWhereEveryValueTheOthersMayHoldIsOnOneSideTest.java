package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.WhatARelationLeavesUndivided.Leaves;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Line;
import souther.compiler.inputs.WhatARelationLeavesUndivided.SettledRun;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactCut;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which values of a term settle a relation, asked of where the other terms may lie, and whether
 * every other value of it is shown to leave the relation either way.
 *
 * <p>Each case is a pair, as for what a relation leaves undivided: the relation as it stands, and
 * the one change that moves the answer. A value is settled where everything the others could be is
 * on one side; it is left either way only where some other term is shown to reach both sides.
 */
class ARelationIsSettledOnlyWhereEveryValueTheOthersMayHoldIsOnOneSideTest {

    private static final BigInteger GREATEST_INT = BigInteger.valueOf(Long.MAX_VALUE);

    private static NumericDomain.Bounds run(Long low, Long high) {
        return new NumericDomain.Bounds(low == null ? null : Endpoint.inclusive(Count.of(low)),
                high == null ? null : Endpoint.inclusive(Count.of(high)));
    }

    private static WhatARelationLeavesUndivided.Term<String> term(String place, long weight,
                                                                 NumericDomain.Bounds holds,
                                                                 NumericDomain.Bounds realizes) {
        return new WhatARelationLeavesUndivided.Term<>(List.of(place), ExactRatio.of(weight), holds,
                realizes, null, true, Granularity.DISCRETE, INTS, place);
    }

    /** Where an {@code Int} stops. */
    private static final NumericDomain.Bounds INTS = run(Long.MIN_VALUE, Long.MAX_VALUE);

    private static WhatARelationLeavesUndivided.Term<String> denseTerm(
            String place, long weight, NumericDomain.Bounds holds, NumericDomain.Bounds realizes) {
        return new WhatARelationLeavesUndivided.Term<>(List.of(place), ExactRatio.of(weight),
                holds, realizes, null, true, Granularity.DENSE, NumericDomain.Bounds.OPEN);
    }

    private static Leaves leavesOf(List<WhatARelationLeavesUndivided.Term<String>> terms, int at,
                                   long constant, Rel relation) {
        return WhatARelationLeavesUndivided.leavesOf(terms, at, ExactRatio.of(constant), relation,
                String::equals, (one, other) -> true, Granularity.DISCRETE, GREATEST_INT);
    }

    private static Leaves ofAProduct(NumericDomain.Bounds it, NumericDomain.Bounds other,
                                     NumericDomain.Bounds reached, long level, Rel relation,
                                     boolean apart) {
        return WhatARelationLeavesUndivided.leavesOfAProduct(term("x", 1, it, it),
                term("y", 1, other, reached), ExactRatio.of(level), relation, apart,
                GREATEST_INT);
    }

    private static SettledRun settled(Long from, Long to, boolean holds) {
        return SettledRun.whole(from == null ? null : BigInteger.valueOf(from),
                to == null ? null : BigInteger.valueOf(to), holds);
    }

    private static Leaves.Settled settledIn(Long least, Long greatest, SettledRun... runs) {
        return Leaves.Settled.ofWhole(List.of(runs),
                least == null ? null : BigInteger.valueOf(least),
                greatest == null ? null : BigInteger.valueOf(greatest));
    }

    private static Line line(Rel relation, long at) {
        return new Line(relation, ExactRatio.of(at));
    }

    /**
     * {@code a + c < b} with {@code a} and {@code b} from one to twelve and {@code c} from one to
     * thirty-one: {@code a} at eleven or twelve fails it whatever the others hold, and below that
     * the other two together come to a sum {@code c - b} from minus eleven to thirty, which is
     * either side of every level {@code a} would need. No one of them does alone, and the other
     * terms count together only where each is shown to take its ends and none is tied to another.
     */
    @Test
    void severalTermsTogetherLeaveTheRestEitherWayWhereNoOneOfThemDoes() {
        var a = term("a", 1, run(1L, 12L), run(1L, 12L));
        var c = term("c", 1, run(1L, 31L), run(1L, 31L));
        var b = term("b", -1, run(1L, 12L), run(1L, 12L));
        assertEquals(settledIn(1L, 12L, settled(11L, 12L, false)),
                leavesOf(List.of(a, c, b), 0, 0, Rel.LT));
        assertEquals(settledIn(1L, 31L, settled(11L, 31L, false)),
                leavesOf(List.of(a, c, b), 1, 0, Rel.LT));
        assertEquals(settledIn(1L, 12L, settled(1L, 2L, false)),
                leavesOf(List.of(a, c, b), 2, 0, Rel.LT));

        var unseenC = term("c", 1, run(1L, 31L), null);
        assertNull(leavesOf(List.of(a, unseenC, b), 0, 0, Rel.LT));

        assertNull(WhatARelationLeavesUndivided.leavesOf(List.of(a, c, b), 0, ExactRatio.of(0),
                Rel.LT, String::equals, (one, other) -> one + other != 1,
                Granularity.DISCRETE, GREATEST_INT));
    }

    /**
     * {@code a + c <= b} fails from twelve on and {@code a + c > b} holds there: the side that
     * asks to be strictly past the level is the other one than for {@code <}, and a run of one
     * value is a class.
     */
    @Test
    void theStrictSideOfTheLevelFollowsTheRelation() {
        var a = term("a", 1, run(1L, 12L), run(1L, 12L));
        var c = term("c", 1, run(1L, 31L), run(1L, 31L));
        var b = term("b", -1, run(1L, 12L), run(1L, 12L));
        assertEquals(settledIn(1L, 12L, settled(12L, 12L, false)),
                leavesOf(List.of(a, c, b), 0, 0, Rel.LE));
        assertEquals(settledIn(1L, 12L, settled(12L, 12L, true)),
                leavesOf(List.of(a, c, b), 0, 0, Rel.GT));
    }

    /**
     * The upper end of a run of whole numbers that is left out is the whole number below it, so
     * {@code c} below thirty-two is {@code c} to thirty-one.
     */
    @Test
    void aRunOfWholeNumbersLeavingItsUpperEndOutIsTheRunBelowIt() {
        var leftOut = new NumericDomain.Bounds(Endpoint.inclusive(Count.of(1L)),
                new Endpoint(Count.of(32L), false));
        var a = term("a", 1, run(1L, 12L), run(1L, 12L));
        var c = term("c", 1, leftOut, leftOut);
        var b = term("b", -1, run(1L, 12L), run(1L, 12L));
        assertEquals(settledIn(1L, 12L, settled(11L, 12L, false)),
                leavesOf(List.of(a, c, b), 0, 0, Rel.LT));
    }

    /**
     * {@code a <= b + c} over decimals is not read from the others together: a decimal sum or
     * product stops for the scale of its factors and not only for the size of the number, so the
     * ends of the others are no witness whatever their size. With {@code a} from one to nine and
     * the others to five each, only the two of them together come past every {@code a}, and that
     * is not asked. With {@code c} and {@code d} between minus and plus the least decimal there
     * is, every product with a written {@code 1.0} stops, and the two rows the others' ends give
     * are rows nothing computes. {@code b} and {@code d} held at nought, though, leave {@code a}
     * and {@code c} held against each other alone, which the reading of two terms answers as it
     * answers them without the rest.
     */
    @Test
    void decimalsAreNotReadTogetherForTheirArithmeticStopsForMoreThanTheirSize() {
        var a = denseTerm("a", 1, run(1L, 9L), run(1L, 9L));
        var b = denseTerm("b", -1, run(0L, 5L), run(0L, 5L));
        var c = denseTerm("c", -1, run(0L, 5L), run(0L, 5L));
        assertNull(WhatARelationLeavesUndivided.leavesOf(List.of(a, b, c), 0, ExactRatio.of(0),
                Rel.LE, String::equals, (one, other) -> true, Granularity.DENSE, null));

        NumericDomain.Bounds tiny = new NumericDomain.Bounds(
                Endpoint.inclusive(new Count(new BigDecimal(BigInteger.ONE.negate(),
                        Integer.MAX_VALUE))),
                Endpoint.inclusive(new Count(new BigDecimal(BigInteger.ONE, Integer.MAX_VALUE))));
        var nought = denseTerm("a", 1, run(0L, 0L), run(0L, 0L));
        var beside = denseTerm("b", -1, run(0L, 0L), run(0L, 0L));
        var plus = denseTerm("c", -1, tiny, tiny);
        var more = denseTerm("d", -1, tiny, tiny);
        assertEquals(new Leaves.Undivided(), WhatARelationLeavesUndivided.leavesOf(
                List.of(nought, beside, plus, more), 0, ExactRatio.of(0), Rel.LT, String::equals,
                (one, other) -> true, Granularity.DENSE, null));
        assertEquals(new Leaves.Undivided(), WhatARelationLeavesUndivided.leavesOf(
                List.of(nought, plus), 0, ExactRatio.of(0), Rel.LT, String::equals,
                (one, other) -> true, Granularity.DENSE, null));
    }

    /**
     * A product the arithmetic can not hold is no run, and the reading says nothing and does not
     * throw: the weight is the greatest the exponent of an exact number allows beside an end that
     * has none to spare.
     */
    @Test
    void aProductNoNumberHoldsLeavesTheReadingUnsaid() {
        ExactRatio end = ExactRatio.of(new BigDecimal(BigInteger.ONE, -Integer.MAX_VALUE));
        List<ExactRatio> powers = new ArrayList<>(List.of(end));
        while (powers.getLast().times(powers.getLast())
                instanceof ExactAnswer.Held<ExactRatio>(ExactRatio squared)) {
            powers.add(squared);
        }
        ExactRatio weight = ExactRatio.ONE;
        for (ExactRatio power : powers.reversed()) {
            if (weight.times(power) instanceof ExactAnswer.Held<ExactRatio>(ExactRatio product)) {
                weight = product;
            }
        }
        assertEquals(true, weight.times(end) instanceof ExactAnswer.Unheld<ExactRatio>);
        NumericDomain.Bounds far = new NumericDomain.Bounds(Endpoint.inclusive(Count.ZERO),
                Endpoint.inclusive(Count.of(new BigDecimal(BigInteger.ONE, -Integer.MAX_VALUE))));
        var a = term("a", 1, run(1L, 12L), run(1L, 12L));
        var b = new WhatARelationLeavesUndivided.Term<>(List.of("b"), weight, far, far, null,
                true, Granularity.DENSE, NumericDomain.Bounds.OPEN);
        var c = term("c", -1, run(1L, 12L), run(1L, 12L));
        assertNull(leavesOf(List.of(a, b, c), 0, 0, Rel.LT));
    }

    /**
     * A run whose ends have crossed holds no value, so a term shown to take it takes none and is
     * no witness at either end: {@code a + b + c < 0} with {@code b} shown to take nothing says
     * nothing of {@code a}. What {@code b} is shown to take is no part of what is said of
     * {@code b}, which {@code a} and {@code c} reach both sides of.
     */
    @Test
    void aTermShownToTakeNoValueIsNoWitness() {
        var a = term("a", 1, run(-1L, 1L), run(-1L, 1L));
        var c = term("c", 1, run(-3L, 3L), run(-3L, 3L));
        var takesNone = term("b", 1, run(-3L, 3L), run(1L, 0L));
        assertNull(leavesOf(List.of(a, takesNone, c), 0, 0, Rel.LT));
        assertEquals(new Leaves.Undivided(), leavesOf(List.of(takesNone, a, c), 0, 0, Rel.LT));
    }

    /** {@code a + b + d - s - 150000 >= 0} for an {@code a} from {@code low} to {@code high}, with
     *  as many of {@code b} and {@code d} as {@code positive} says. */
    private static Leaves ofTheAmounts(Long low, Long high, int positive) {
        return ofTheAmounts(low, high, positive, Rel.GE, 1);
    }

    /** The same relation held as {@code relation} where {@code sign} is one, and turned round
     *  where it is minus one: every weight and the constant negated, and the relation reversed. */
    private static Leaves ofTheAmounts(Long low, Long high, int positive, Rel relation, int sign) {
        var amount = run(0L, Long.MAX_VALUE);
        List<WhatARelationLeavesUndivided.Term<String>> terms = new ArrayList<>();
        terms.add(term("a", sign, run(low, high), run(low, high)));
        for (String place : List.of("b", "d").subList(0, positive)) {
            terms.add(term(place, sign, amount, amount));
        }
        terms.add(term("s", -sign, amount, amount));
        Rel held = sign > 0 ? relation : switch (relation) {
            case GE -> Rel.LE;
            case GT -> Rel.LT;
            case LE -> Rel.GE;
            case LT -> Rel.GT;
            default -> relation;
        };
        return leavesOf(terms, 0, -150000L * sign, held);
    }

    /**
     * {@code a + b + d - s - 150000 >= 0} over amounts from nought to the greatest {@code Int}.
     * Below 150000 only {@code b} reaches the true side, with the false side at nought. From
     * 150000 on {@code b} reaches no false side, since {@code a} is the row's own, and
     * only {@code s} does. Neither reaches both sides of the whole run, and the run is left either
     * way where each piece of it is reached by one of them: at the join of the two pieces and at
     * each end of the whole.
     */
    @Test
    void aRunIsLeftEitherWayWhereEachPieceOfItIsReachedByOneTerm() {
        long join = 150000L;
        assertEquals(new Leaves.Undivided(), ofTheAmounts(0L, join - 1, 2));
        assertEquals(new Leaves.Undivided(), ofTheAmounts(join, Long.MAX_VALUE - 1, 2));
        assertEquals(new Leaves.Undivided(), ofTheAmounts(0L, Long.MAX_VALUE - 1, 2));
        assertEquals(new Leaves.Undivided(), ofTheAmounts(join - 1, join, 2));
        // With one of the two, d does what b did. With neither, an a below 150000 is false
        // whatever s is, and the run is not left either way across.
        assertEquals(new Leaves.Undivided(), ofTheAmounts(0L, Long.MAX_VALUE - 1, 1));
        assertNotEquals(new Leaves.Undivided(), ofTheAmounts(0L, Long.MAX_VALUE - 1, 0));
        assertEquals(new Leaves.Undivided(), ofTheAmounts(join, Long.MAX_VALUE - 1, 0));
    }

    /**
     * Where one term's reach ends and the other's begins moves by one with the relation being
     * strict and with the sign of the term asked of: {@code a + b - s > 150000} is false at
     * 150000 by {@code b} and true at 150001 by {@code s}'s absence, and the same relation turned
     * round has the join the other side of the cut. The pieces beside a cut are asked as pieces
     * of their own for that, whichever way the relation is held.
     */
    @Test
    void theJoinOfTwoPiecesMovesWithTheStrictnessOfTheRelationAndTheSignOfTheTerm() {
        for (Rel relation : List.of(Rel.GE, Rel.GT)) {
            for (int sign : List.of(1, -1)) {
                assertEquals(new Leaves.Undivided(),
                        ofTheAmounts(0L, Long.MAX_VALUE - 2, 1, relation, sign),
                        relation + " held " + sign);
            }
        }
    }

    /**
     * Where the run takes the greatest {@code Int}, the value is not settled true. The form is
     * only known as a weighed sum and a constant, and a program adding it up from the left has a
     * false row there: {@code a} the greatest, {@code b} and {@code d} nought and {@code s} the
     * greatest less 149999, whose sums along the way are the greatest, the greatest, 149999 and
     * -1. Which rows are computed is the operation's to say, and none is said, so nothing is
     * shown.
     */
    @Test
    void aValueIsNotSettledByTheArithmeticWhereTheOrderTheProgramAddsInIsNotKnown() {
        assertNull(ofTheAmounts(0L, Long.MAX_VALUE, 2));
    }

    /** A greatest value no row of the small runs comes near. */
    private static final long LET_GO = 1000;

    private static final NumericDomain.Bounds[] SMALL_RUNS = {
        run(0L, 4L), run(-2L, 2L), run(1L, 4L), run(0L, 1L)};

    /**
     * Whether a row of weighed addends and the constant is computed where the type stops at
     * {@code greatest}: its positive addends together and its negative ones together are no
     * further from nought than the greatest.
     */
    private static boolean computes(long greatest, List<Long> addends) {
        long up = 0;
        long down = 0;
        for (long each : addends) {
            if (each > 0) {
                up += each;
            } else {
                down -= each;
            }
        }
        return up <= greatest && down <= greatest;
    }

    private static long endOf(Endpoint end) {
        return ((Count) end.at()).at().longValueExact();
    }

    private static boolean takes(long value, NumericDomain.Bounds bounds) {
        return endOf(bounds.min()) <= value && value <= endOf(bounds.max());
    }

    /**
     * Every answer a small relation is given is what its rows say. Over a type that stops at four,
     * three terms of weight one or minus one, runs with and without nought, and
     * constants either side of nought, every row there is is enumerated: what is said to be left
     * either way has a computed row on each side, and what is said to be settled has no computed
     * row on the other side. Nothing is said of a relation that is not read.
     */
    @Test
    void whatIsSaidOfASmallRelationIsWhatItsComputedRowsSay() {
        long greatest = 4;
        int said = 0;
        for (int terms : new int[] {3}) {
            for (int signs = 0; signs < (1 << terms); signs++) {
                for (int runs = 0; runs < Math.pow(SMALL_RUNS.length, terms); runs++) {
                    List<WhatARelationLeavesUndivided.Term<String>> list = new ArrayList<>();
                    int rest = runs;
                    for (int i = 0; i < terms; i++) {
                        NumericDomain.Bounds held = SMALL_RUNS[rest % SMALL_RUNS.length];
                        rest /= SMALL_RUNS.length;
                        list.add(new WhatARelationLeavesUndivided.Term<>(List.of("t" + i),
                                ExactRatio.of((signs >> i & 1) == 0 ? 1 : -1), held, held, null,
                                true, Granularity.DISCRETE, run(-greatest - 1, greatest)));
                    }
                    for (long constant : new long[] {-6, -3, 0, 3}) {
                        for (Rel relation : new Rel[] {Rel.GE, Rel.LT}) {
                            for (int at = 0; at < 2; at++) {
                                said += checked(list, at, constant, relation, greatest);
                            }
                        }
                    }
                }
            }
        }
        assertTrue(said > 100, "some relation is read, or this asks nothing: " + said);
    }

    /** 1 where something is said of the relation and it is what the rows say, 0 where not. */
    private static int checked(List<WhatARelationLeavesUndivided.Term<String>> terms, int at,
                               long constant, Rel relation, long greatest) {
        Leaves leaves = WhatARelationLeavesUndivided.leavesOf(terms, at,
                ExactRatio.of(constant), relation, String::equals, (one, other) -> true,
                Granularity.DISCRETE, BigInteger.valueOf(greatest));
        if (leaves == null) {
            return 0;
        }
        NumericDomain.Bounds held = terms.get(at).holds();
        String where = leaves + " for " + terms.stream().map(
                each -> each.weight() + "*" + endOf(each.holds().min()) + ".."
                        + endOf(each.holds().max())).toList() + " at " + at + " " + constant
                + " " + relation;
        for (long each = endOf(held.min()); each <= endOf(held.max()); each++) {
            long value = each;
            boolean[] sides = sidesOf(terms, at, value, constant, relation, greatest);
            // Left undivided says the relation draws no line on the term, and not that every value
            // has a computed row on each side: at an end of the type the size alone may leave a
            // side without one, where the sum is computed and compared with the constant and not
            // added up with it. So a side a row is missing from is the arithmetic's only where
            // rows on each side stand once the arithmetic is let go.
            // Asked only where the computed rows leave a side out, which is rare.
            switch (leaves) {
                case Leaves.Undivided _ -> assertTrue((sides[0] && sides[1])
                                || bothSidesOnceLetGo(terms, at, value, constant, relation),
                        "left either way at " + value + ": " + where);
                case Leaves.Settled settled -> {
                    // A value no row computes is outside what is said of the term.
                    if (value < settled.least().at().floor().orNull().longValueExact()
                            || value > settled.greatest().at().floor().orNull().longValueExact()) {
                        continue;
                    }
                    SettledRun inside = settled.runs().stream()
                            .filter(run -> within(run, value)).findFirst().orElse(null);
                    if (inside == null) {
                        assertTrue((sides[0] && sides[1])
                                        || bothSidesOnceLetGo(terms, at, value, constant, relation),
                                "left either way at " + value + ": " + where);
                    } else {
                        // Settled is that no computed row is on the other side. A value no row
                        // computes at all is settled both ways, and a run holding one is still a
                        // class by its values that have a row.
                        assertFalse(sides[inside.holds() ? 1 : 0],
                                "settled " + inside.holds() + " at " + value + ": " + where);
                    }
                }
            }
        }
        return 1;
    }

    private static boolean within(SettledRun run, long value) {
        ExactRatio at = ExactRatio.of(value);
        return (run.from() == null || at.compareTo(run.from().at()) > 0
                || (run.from().inclusive() && at.compareTo(run.from().at()) == 0))
                && (run.to() == null || at.compareTo(run.to().at()) < 0
                || (run.to().inclusive() && at.compareTo(run.to().at()) == 0));
    }

    /** Whether, with the arithmetic let go, some row holds the relation and some row fails it. */
    private static boolean bothSidesOnceLetGo(
            List<WhatARelationLeavesUndivided.Term<String>> terms, int at, long value,
            long constant, Rel relation) {
        boolean[] sides = sidesOf(terms, at, value, constant, relation, LET_GO);
        return sides[0] && sides[1];
    }

    /** Whether some computed row holds the relation, and whether some computed row fails it. */
    private static boolean[] sidesOf(List<WhatARelationLeavesUndivided.Term<String>> terms,
                                     int at, long value, long constant, Rel relation,
                                     long greatest) {
        boolean[] sides = new boolean[2];
        enumerate(terms, 0, at, value, new ArrayList<>(List.of(constant)), relation, greatest,
                sides);
        return sides;
    }

    private static void enumerate(List<WhatARelationLeavesUndivided.Term<String>> terms, int next,
                                  int at, long value, List<Long> addends, Rel relation,
                                  long greatest, boolean[] sides) {
        if (next == terms.size()) {
            if (computes(greatest, addends)) {
                long sum = addends.stream().mapToLong(Long::longValue).sum();
                sides[relation.holds(Long.signum(sum)) ? 0 : 1] = true;
            }
            return;
        }
        long weight = terms.get(next).weight().isWhole()
                ? terms.get(next).weight().floor().orNull().longValue() : 0;
        if (next == at) {
            addends.add(weight * value);
            enumerate(terms, next + 1, at, value, addends, relation, greatest, sides);
            addends.removeLast();
            return;
        }
        for (long each = -greatest - 1; each <= greatest; each++) {
            if (takes(each, terms.get(next).holds())) {
                addends.add(weight * each);
                enumerate(terms, next + 1, at, value, addends, relation, greatest, sides);
                addends.removeLast();
            }
        }
    }

    /**
     * {@code a + c >= b} over the same runs is settled the other way, true from eleven on.
     */
    @Test
    void theSameTermsHeldTheOtherWayAreSettledTheOtherWay() {
        var a = term("a", 1, run(1L, 12L), run(1L, 12L));
        var c = term("c", 1, run(1L, 31L), run(1L, 31L));
        var b = term("b", -1, run(1L, 12L), run(1L, 12L));
        assertEquals(settledIn(1L, 12L, settled(11L, 12L, true)),
                leavesOf(List.of(a, c, b), 0, 0, Rel.GE));
    }

    /**
     * {@code a < b + 3 * c + 4 * d} with {@code a} at one below the greatest {@code Int}, {@code b}
     * at two below, and {@code c} and {@code d} nought or one. Held as {@code a - b - 3c - 4d < 0}
     * the sums along the way stay inside the type at every row, and held as the program writes
     * it the sum of the others passes where the type stops at {@code c} or {@code d} one. The
     * form does not say which, so the value is not shown settled either way.
     */
    @Test
    void theOthersAreNotJudgedWhereTheOrderTheProgramAddsInIsNotKnown() {
        long max = Long.MAX_VALUE;
        var a = term("a", 1, run(max - 1, max - 1), run(max - 1, max - 1));
        var b = term("b", -1, run(max - 2, max - 2), run(max - 2, max - 2));
        var c = term("c", -3, run(0L, 1L), run(0L, 1L));
        var d = term("d", -4, run(0L, 1L), run(0L, 1L));
        assertNull(leavesOf(List.of(a, b, c, d), 0, 0, Rel.LT));
    }

    /** An {@code Int} operation of the terms called by the names, each weighed by the number
     *  after it, and {@code constant}. */
    private static WhatARelationLeavesUndivided.IntSum anIntSum(long constant,
                                                               Object... namesAndWeights) {
        Map<Object, ExactRatio> coefs = new LinkedHashMap<>();
        for (int i = 0; i < namesAndWeights.length; i += 2) {
            coefs.put(namesAndWeights[i], ExactRatio.of((Integer) namesAndWeights[i + 1]));
        }
        return new WhatARelationLeavesUndivided.IntSum(coefs, ExactRatio.of(constant),
                BigInteger.valueOf(Long.MIN_VALUE), GREATEST_INT);
    }

    private static Leaves ofTheAmountsAddedUp(boolean exact,
                                              WhatARelationLeavesUndivided.IntSum... sums) {
        var amount = run(0L, Long.MAX_VALUE);
        return WhatARelationLeavesUndivided.leavesOf(List.of(
                term("a", 1, amount, amount), term("b", 1, amount, amount),
                term("d", 1, amount, amount), term("s", -1, amount, amount)), 0,
                ExactRatio.of(-150000L), Rel.GE, String::equals, (one, other) -> true,
                Granularity.DISCRETE, GREATEST_INT, List.of(),
                WhatARelationLeavesUndivided.Operations.read(List.of(sums), exact));
    }

    /**
     * {@code a + b + d >= s + 150000} over amounts from nought: the program adds 150000 to
     * {@code s}, so a row has an {@code s} no further than the greatest less 150000, and at the
     * greatest {@code a} no row fails. The value is settled true by the arithmetic alone, a line
     * of the type and not of the model, which draws none.
     */
    @Test
    void aSumTheProgramWorksOutCutsTheTermsItAdds() {
        Leaves.Settled whole = (Leaves.Settled) ofTheAmountsAddedUp(true,
                anIntSum(0, "a", 1, "b", 1), anIntSum(0, "a", 1, "b", 1, "d", 1),
                anIntSum(150000, "s", 1));
        assertEquals(List.of(settled(Long.MAX_VALUE, Long.MAX_VALUE, true)), whole.runs());
        assertEquals(List.of(line(Rel.GE, Long.MAX_VALUE)), whole.ofTheTypeAlone());
    }

    /**
     * {@code a + b + d - s - 150000 >= 0}: the same relation worked out from the left. Nothing
     * adds 150000 to {@code s}, and the row {@code a} the greatest, {@code b} and {@code d}
     * nought, {@code s} the greatest less 149999 is computed — its sums are the greatest, the
     * greatest, 149999 and minus one — and fails. The greatest {@code a} is no value that settles
     * the relation true.
     */
    @Test
    void aConstantTheProgramSubtractsIsNoCutOnTheTermThatIsSubtractedFrom() {
        Leaves leaves = ofTheAmountsAddedUp(true,
                anIntSum(0, "a", 1, "b", 1), anIntSum(0, "a", 1, "b", 1, "d", 1),
                anIntSum(0, "a", 1, "b", 1, "d", 1, "s", -1),
                anIntSum(-150000, "a", 1, "b", 1, "d", 1, "s", -1));
        assertFalse(leaves instanceof Leaves.Settled settled
                && settled.runs().stream().anyMatch(each -> each.holds()),
                () -> "the greatest a is settled true: " + leaves);
    }

    /**
     * {@code a + b >= 0} written {@code (a + 1) + (b - 1) >= 0}: one value, and two programs.
     * The second adds 1 to {@code a}, which is no row at the greatest {@code a}, and the first
     * adds nothing to it. What the relation leaves is not the same for the two, though the form
     * they are cut as is.
     */
    @Test
    void twoProgramsOfOneFormAreNotOneEvidence() {
        var either = run(Long.MIN_VALUE, Long.MAX_VALUE);
        List<WhatARelationLeavesUndivided.Term<String>> terms = List.of(
                term("a", 1, either, either), term("b", 1, either, either));
        Leaves plain = WhatARelationLeavesUndivided.leavesOf(terms, 0, ExactRatio.ZERO, Rel.GE,
                String::equals, (one, other) -> true, Granularity.DISCRETE, GREATEST_INT,
                List.of(), WhatARelationLeavesUndivided.Operations.read(
                        List.of(anIntSum(0, "a", 1, "b", 1)), true));
        Leaves shifted = WhatARelationLeavesUndivided.leavesOf(terms, 0, ExactRatio.ZERO, Rel.GE,
                String::equals, (one, other) -> true, Granularity.DISCRETE, GREATEST_INT,
                List.of(), WhatARelationLeavesUndivided.Operations.read(
                        List.of(anIntSum(1, "a", 1), anIntSum(-1, "b", 1),
                                anIntSum(0, "a", 1, "b", 1)), true));
        assertNotEquals(plain, shifted);
    }

    /**
     * {@code n - len <= 0}, {@code len} from nought on: every {@code n} at or below nought holds
     * it whatever {@code len} is, and from one on {@code len} is either side of it. Where
     * {@code len} may be anything, nothing is on one side, and {@code n} is undivided.
     */
    @Test
    void aValueEveryOtherValueIsOnOneSideOfSettlesTheRelation() {
        Leaves fromNought = leavesOf(List.of(
                term("n", 1, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN),
                term("len", -1, run(0L, null), run(0L, null))), 0, 0, Rel.LE);
        assertEquals(settledIn(null, null, settled(null, 0L, true)), fromNought);
        assertEquals(List.of(line(Rel.LE, 0)), ((Leaves.Settled) fromNought).linesOfTheModel());

        assertEquals(new Leaves.Undivided(), leavesOf(List.of(
                term("n", 1, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN),
                term("len", -1, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN)), 0, 0,
                Rel.LE));
    }

    /**
     * {@code k - count <= 0}, the count what an operation answers, from one on, and {@code k} any
     * {@code Int}. At the greatest count no {@code k} is greater, so the relation holds there
     * whatever {@code k} is; below it {@code k} is either side of every count. The line at the
     * greatest count is there only because {@code k} stops where its type does: free to run on,
     * {@code k} would be above that count too. So it is kept, and kept apart as the type's.
     */
    @Test
    void aValueSettledOnlyBecauseTheOtherStopsWhereItsTypeDoesIsTheTypesLine() {
        long most = Long.MAX_VALUE;
        Leaves.Settled count = (Leaves.Settled) leavesOf(List.of(
                term("k", 1, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN),
                answer("count", -1, run(1L, null), run(1L, null))), 1, 0, Rel.LE);
        assertEquals(List.of(settled(most, most, true)), count.runs());
        assertEquals(List.of(line(Rel.GE, most)), count.ofTheTypeAlone());
        assertEquals(List.of(), count.linesOfTheModel());

        // A rule that puts k at the greatest Int at most draws the same line, and it is the
        // model's: the rule stops k there, wherever its type stops.
        Leaves.Settled ruled = (Leaves.Settled) leavesOf(List.of(
                term("k", 1, run(null, most), NumericDomain.Bounds.OPEN),
                answer("count", -1, run(1L, null), run(1L, null))), 1, 0, Rel.LE);
        assertEquals(List.of(line(Rel.GE, most)), ruled.linesOfTheModel());
        assertEquals(List.of(), ruled.ofTheTypeAlone());
    }

    /**
     * The same count, with {@code k} not shown to take any value: that the greatest count is
     * settled by the type alone says nothing of the counts below it, which no {@code k} is shown
     * to reach either side of, and nothing is shown.
     */
    @Test
    void aLineOfTheTypeShowsNothingOfTheValuesNoOtherTermIsShownToReach() {
        assertNull(leavesOf(List.of(
                term("k", 1, NumericDomain.Bounds.OPEN, null),
                answer("count", -1, run(1L, null), run(1L, null))), 1, 0, Rel.LE));
    }

    /**
     * {@code x - y - 2 < 0}, both any {@code Int}: the rows that are computed depend on whether
     * the program adds 2 to {@code y} or takes it off {@code x} and {@code y}, and the form says
     * neither, so no value is shown settled by where the type stops.
     */
    @Test
    void aRunIsNotCutWhereTheTypeStopsWhenTheOperationIsNotKnown() {
        assertNull(leavesOf(List.of(
                answer("x", 1, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN),
                answer("y", -1, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN)), 1, -2,
                Rel.LT));
    }

    /**
     * {@code x - y <= 0}, both from nought on and {@code y} shown to take every {@code Int} from
     * nought. At nought {@code x} holds it whatever {@code y} is, because the rules hold {@code y}
     * at nought or above: a line of the model's, whether or not the values of {@code x} past every
     * {@code y} the type writes are shown reached.
     */
    @Test
    void aLineTheRulesDrawStaysTheModelsWhereTheFreeTermsShowNothing() {
        long most = Long.MAX_VALUE;
        Leaves.Settled x = (Leaves.Settled) leavesOf(List.of(
                term("x", 1, run(0L, null), run(0L, null)),
                term("y", -1, run(0L, null), run(0L, most))), 0, 0, Rel.LE);
        assertEquals(List.of(line(Rel.LE, 0)), x.linesOfTheModel());
    }

    /**
     * {@code x - y + z - M > 0}, {@code M} the greatest {@code Int}: true only where
     * {@code x - y + z} passes the greatest {@code Int}, which no row computes. Holding {@code z}
     * at {@code M} brings the constant to nought, and {@code x - y > 0} is reached at every
     * {@code x}; but every row it reaches the true side with is one whose sum passes the type.
     */
    @Test
    void aTermHeldWhereItCancelsTheConstantIsNoWitnessWhereTheRowPassesTheType() {
        long most = Long.MAX_VALUE;
        Leaves x = leavesOf(List.of(
                term("x", 1, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN),
                term("y", -1, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN),
                term("z", 1, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN)), 0, -most,
                Rel.GT);
        assertFalse(x instanceof Leaves.Undivided, () -> "x: " + x);
    }

    /**
     * {@code x - y - M > 0} with {@code x} from nought to ten: a {@code y} below
     * {@code x - M} is one every {@code y} the type writes is, but {@code x - y} then passes the
     * greatest {@code Int}, so no row is on the true side.
     */
    @Test
    void anOtherTermIsNoWitnessWhereTheRowItStandsInPassesTheType() {
        long most = Long.MAX_VALUE;
        Leaves x = leavesOf(List.of(
                term("x", 1, run(0L, 10L), run(0L, 10L)),
                term("y", -1, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN)), 0, -most,
                Rel.GT);
        assertFalse(x instanceof Leaves.Undivided, () -> "x: " + x);
    }

    /** A term that is what an operation answers, counted on the {@code Int}s. */
    private static WhatARelationLeavesUndivided.Term<String> answer(String place, long weight,
                                                                   NumericDomain.Bounds holds,
                                                                   NumericDomain.Bounds realizes) {
        return new WhatARelationLeavesUndivided.Term<>(List.of(place), ExactRatio.of(weight), holds,
                realizes, null, false, Granularity.DISCRETE, INTS);
    }

    /**
     * {@code x * y >= 1000} with {@code x} at the least value of the type, whose product with minus
     * one passes where the type stops. That the rule fails there with every {@code y} the run can
     * multiply it by is the end of the type, as {@code x < y} fails at the greatest {@code x}, and
     * draws no line: beside the next value up, which minus one takes over the level, and alone,
     * {@code x} is undivided. Where the one pair a run would be settled by is that one, the run
     * stands only past the type, and nothing is shown.
     */
    @Test
    void theLeastValueAloneIsTheEndOfTheTypeAndDrawsNoLine() {
        long least = Long.MIN_VALUE;
        assertEquals(new Leaves.Undivided(), ofAProduct(run(least, least + 1),
                NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN, 1000, Rel.GE, true));
        assertEquals(new Leaves.Undivided(), ofAProduct(run(least, least), run(-1L, 1L),
                run(-1L, 1L), 1000, Rel.GE, true));
        assertNull(ofAProduct(run(least, least), run(-1L, -1L), run(-1L, -1L), 1000, Rel.GE,
                true));
    }

    /**
     * {@code 4 * x + y >= 0}, {@code y} from the least value of the type to ten above it: the
     * values settling it are {@code x} from two to the sixty-first on, and four times any of them
     * passes where the type stops, so no row of that run has a value and it is no class — nothing
     * is shown. With {@code y} from nought to ten the run starts at nought, which has rows.
     */
    @Test
    void aRunWhoseEveryRowPassesWhereTheTypeStopsIsNoClass() {
        long least = Long.MIN_VALUE;
        assertNull(leavesOf(List.of(
                term("x", 4, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN),
                term("y", 1, run(least, least + 10), run(least, least + 10))), 0, 0, Rel.GE));

        Leaves near = leavesOf(List.of(
                term("x", 4, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN),
                term("y", 1, run(0L, 10L), run(0L, 10L))), 0, 0, Rel.GE);
        assertEquals(List.of(settled(null, -3L, false), settled(0L, null, true)),
                ((Leaves.Settled) near).runs());
    }

    /**
     * {@code x + y >= 1000}, each from one to a hundred thousand: from 999 on {@code x} holds it
     * whatever {@code y} is, and below that {@code y} reaches either side. Where {@code y} is
     * shown to reach nothing, the values below are not shown either way, and nothing is answered.
     */
    @Test
    void theValuesLeftBetweenTheSettledRunsAreAskedWhatTheOtherReaches() {
        NumericDomain.Bounds both = run(1L, 100_000L);
        Leaves reached = leavesOf(List.of(term("x", 1, both, both), term("y", 1, both, both)), 0,
                -1000, Rel.GE);
        assertEquals(settledIn(1L, 100_000L, settled(999L, 100_000L, true)), reached);
        assertEquals(List.of(line(Rel.GE, 999)), ((Leaves.Settled) reached).lines());

        assertNull(leavesOf(List.of(term("x", 1, both, both), term("y", 1, both, null)), 0, -1000,
                Rel.GE));
    }

    /**
     * {@code x * y >= 1000} over every whole number: nought fails it whatever {@code y} is, and
     * every other {@code x} leaves {@code y} either side of the level over it. Held away from
     * nought, {@code x} is undivided.
     */
    @Test
    void noughtSettlesAProductWhateverTheOtherFactorIs() {
        Leaves everywhere = ofAProduct(NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN,
                NumericDomain.Bounds.OPEN, 1000, Rel.GE, true);
        assertEquals(settledIn(null, null, settled(0L, 0L, false)), everywhere);
        assertEquals(List.of(line(Rel.EQ, 0)), ((Leaves.Settled) everywhere).lines());

        assertEquals(new Leaves.Undivided(), ofAProduct(run(1L, null), NumericDomain.Bounds.OPEN,
                NumericDomain.Bounds.OPEN, 1000, Rel.GE, true));
    }

    /**
     * Each from one to a hundred thousand: from a thousand on, {@code x} holds it whatever
     * {@code y} is, and below that {@code y} is either side of the level over it. With {@code y}
     * from two, the values from five hundred on hold it.
     */
    @Test
    void aFactorFarEnoughFromNoughtSettlesTheProductAlone() {
        NumericDomain.Bounds both = run(1L, 100_000L);
        Leaves fromOne = ofAProduct(both, both, both, 1000, Rel.GE, true);
        assertEquals(settledIn(1L, 100_000L, settled(1000L, 100_000L, true)), fromOne);
        assertEquals(List.of(line(Rel.GE, 1000)), ((Leaves.Settled) fromOne).lines());

        NumericDomain.Bounds fromTwo = run(2L, 100_000L);
        assertEquals(settledIn(1L, 100_000L, settled(500L, 100_000L, true)),
                ofAProduct(both, fromTwo, fromTwo, 1000, Rel.GE, true));
    }

    /**
     * Which side of the level over a value the other factor has to pass strictly is the one the
     * relation fails on: under {@code x * y >= 10}, {@code x} at one needs a {@code y} below ten
     * and one at ten or above, and {@code y} from five to ten has both, ten at its end. With
     * {@code y} only up to nine it has no value the relation holds at, and {@code x} at one fails
     * it whatever {@code y} is; {@code x} at two holds it either way.
     */
    @Test
    void theOtherFactorPassesTheLevelStrictlyOnlyOnTheSideTheRelationFailsOn() {
        NumericDomain.Bounds oneOrTwo = run(1L, 2L);
        NumericDomain.Bounds toTen = run(5L, 10L);
        assertEquals(settledIn(1L, 2L, settled(2L, 2L, true)),
                ofAProduct(oneOrTwo, toTen, toTen, 10, Rel.GE, true));

        NumericDomain.Bounds toNine = run(5L, 9L);
        assertEquals(settledIn(1L, 2L, settled(1L, 1L, false), settled(2L, 2L, true)),
                ofAProduct(oneOrTwo, toNine, toNine, 10, Rel.GE, true));
    }

    /**
     * {@code x} held at one, {@code y} from minus ten to ten: {@code y} reaches both signs and
     * never a thousand, so the one value of {@code x} fails it whatever {@code y} is. With
     * {@code y} up to two thousand, it is reached either side.
     */
    @Test
    void reachingBothSignsIsNotReachingBothSidesOfTheLevel() {
        NumericDomain.Bounds one = run(1L, 1L);
        NumericDomain.Bounds near = run(-10L, 10L);
        assertEquals(settledIn(1L, 1L, settled(1L, 1L, false)),
                ofAProduct(one, near, near, 1000, Rel.GE, true));

        NumericDomain.Bounds far = run(-2000L, 2000L);
        assertEquals(new Leaves.Undivided(), ofAProduct(one, far, far, 1000, Rel.GE, true));
    }

    /**
     * Where twice the level is past the greatest value of the type, a value the other has to stand
     * at may put the product past it, and nothing is shown. Within it, the product is answered.
     */
    @Test
    void aLevelTooNearTheEndOfTheTypeShowsNothing() {
        assertNull(ofAProduct(NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN,
                NumericDomain.Bounds.OPEN, 5_000_000_000_000_000_000L, Rel.GE, true));
        assertEquals(settledIn(null, null, settled(0L, 0L, false)),
                ofAProduct(NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN,
                        NumericDomain.Bounds.OPEN, 4_000_000_000_000_000_000L, Rel.GE, true));
    }

    /**
     * Held equal to a level other than nought, which values of {@code x} leave {@code y} a whole
     * number to stand at is which of them divide the level, and nothing is shown. Against nought,
     * nought holds it and every other {@code x} leaves {@code y} at nought or away from it.
     */
    @Test
    void anEqualityIsAnsweredOnlyAgainstNought() {
        assertNull(ofAProduct(NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN,
                NumericDomain.Bounds.OPEN, 1000, Rel.EQ, true));
        assertEquals(settledIn(null, null, settled(0L, 0L, true)),
                ofAProduct(NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN,
                        NumericDomain.Bounds.OPEN, 0, Rel.EQ, true));
    }

    /**
     * Tied to {@code x}, what {@code y} reaches says nothing of the values between the settled
     * ones. A value settled whatever {@code y} is, is settled all the same.
     */
    @Test
    void aTiedFactorShowsOnlyTheValuesSettledWhateverItIs() {
        assertNull(ofAProduct(NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN,
                NumericDomain.Bounds.OPEN, 1000, Rel.GE, false));
        assertEquals(settledIn(0L, 0L, settled(0L, 0L, false)),
                ofAProduct(run(0L, 0L), NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN, 1000,
                        Rel.GE, false));
    }

    /**
     * Two runs settling it opposite ways side by side are parted by one line, and a run of one
     * value with values left either way on both sides is that value singled out. Runs apart are
     * lines apart, and two of one kind on one term stand at different values.
     */
    @Test
    void theLinesPartingTheRunsAreEachOfTheirOwnKind() {
        assertEquals(List.of(line(Rel.LE, 39)),
                settledIn(null, null, settled(null, 39L, false), settled(40L, null, true))
                        .lines());
        assertEquals(List.of(line(Rel.LE, -100), line(Rel.EQ, 0), line(Rel.GE, 100)),
                settledIn(null, null, settled(null, -100L, true), settled(0L, 0L, false),
                        settled(100L, null, true)).lines());
        assertEquals(List.of(line(Rel.GE, 0), line(Rel.LE, 5), line(Rel.GE, 10), line(Rel.LE, 20)),
                settledIn(null, null, settled(0L, 5L, false), settled(10L, 20L, true)).lines());
    }

    private static NumericDomain.Bounds dense(String low, boolean lowIn, String high,
                                              boolean highIn) {
        return new NumericDomain.Bounds(
                new Endpoint(Count.of(new BigDecimal(low)), lowIn),
                new Endpoint(Count.of(new BigDecimal(high)), highIn));
    }

    private static Leaves denseLeavesOf(NumericDomain.Bounds it, NumericDomain.Bounds other,
                                        NumericDomain.Bounds reached, long weight,
                                        Rel relation) {
        return denseLeavesOf(denseTerm("x", 1, it, it), denseTerm("y", weight, other, reached),
                relation);
    }

    private static Leaves denseLeavesOf(WhatARelationLeavesUndivided.Term<String> x,
                                        WhatARelationLeavesUndivided.Term<String> y,
                                        Rel relation) {
        return WhatARelationLeavesUndivided.leavesOf(List.of(x, y), 0, ExactRatio.ZERO, relation,
                String::equals, (one, two) -> true, Granularity.DENSE, null);
    }

    /**
     * {@code x > w} with both between nought and one: nought is settled and a value above it is
     * not, so the one line is {@code x <= 0}, with nought on the settled side. A value just
     * above nought has {@code w} on both sides only because {@code w} takes nought itself, which
     * the run left to ask about does not.
     */
    @Test
    void aDenseTermIsPartedAtTheEndTheOtherTermsRunStopsAt() {
        NumericDomain.Bounds unit = dense("0", true, "1", true);
        Leaves leaves = denseLeavesOf(unit, unit, unit, -1, Rel.GT);
        assertEquals(List.of(line(Rel.LE, 0)), ((Leaves.Settled) leaves).lines());
        assertNull(denseLeavesOf(unit, unit, dense("0.5", true, "1", true), -1, Rel.GT));
    }

    /**
     * {@code x + y < 0} with {@code y} between nought and one, both left out, holds at minus one
     * and fails at nought. Between them a decimal {@code y} is on both sides of {@code -x} except
     * at the one step from an end: at minus a step, the least decimal above nought is not below
     * {@code -x}, so the relation fails there whatever {@code y} is, and nothing is shown.
     */
    @Test
    void anOpenEndTheOtherTermTakesNoValueAtIsNoEndItReachesFromBothSides() {
        NumericDomain.Bounds open = dense("0", false, "1", false);
        assertNull(denseLeavesOf(NumericDomain.Bounds.OPEN, open, open, 1, Rel.LT));
    }

    /** A term that is not dense has no value between an end it leaves out and the next, so the
     *  same open run is not one it reaches the values inside from both sides. */
    @Test
    void aTermThatIsNotDenseIsNotTakenAsOneThatTakesValuesNearAnEndItLeavesOut() {
        NumericDomain.Bounds open = dense("0", false, "1", false);
        assertNull(denseLeavesOf(denseTerm("x", 1, NumericDomain.Bounds.OPEN,
                        NumericDomain.Bounds.OPEN), term("y", 1, open, open), Rel.LT));
    }

    private static Leaves.Settled denseAgainstOne(long weight, Rel relation) {
        NumericDomain.Bounds one = dense("1", true, "1", true);
        return (Leaves.Settled) denseLeavesOf(
                denseTerm("x", weight, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN),
                denseTerm("y", -1, one, one), relation);
    }

    /**
     * {@code 3x == y} with {@code y} always one: the number it holds at is a third, which no
     * decimal is, so no value of {@code x} makes it hold. It fails below the third and above it,
     * and those are one run, there being nothing between to part them.
     */
    @Test
    void aNumberNoDecimalIsIsNoValueTheRelationHoldsAt() {
        Leaves.Settled settled = denseAgainstOne(3, Rel.EQ);
        assertEquals(1, settled.runs().size());
        SettledRun only = settled.runs().getFirst();
        assertEquals(false, only.holds());
        assertNull(only.from());
        assertNull(only.to());
        assertEquals(List.of(), settled.lines());
    }

    /** The relation turned round holds at every decimal, and parts nothing. */
    @Test
    void aNumberNoDecimalIsIsNoValueTheRelationFailsAtEither() {
        Leaves.Settled settled = denseAgainstOne(3, Rel.NE);
        assertEquals(1, settled.runs().size());
        assertEquals(true, settled.runs().getFirst().holds());
        assertEquals(List.of(), settled.lines());
    }

    /** A half is a decimal, so {@code 2x == y} holds there and fails on either side. */
    @Test
    void aNumberADecimalIsIsAValueTheRelationHoldsAt() {
        ExactRatio half = ExactRatio.of(BigInteger.ONE, BigInteger.TWO);
        assertEquals(List.of(new Line(Rel.LT, half), new Line(Rel.LE, half)),
                denseAgainstOne(2, Rel.EQ).lines());
    }

    private static Set<String> undivided(WhatARelationLeavesUndivided.Term<String> x,
                                         WhatARelationLeavesUndivided.Term<String> y, Rel relation) {
        return WhatARelationLeavesUndivided.of(List.of(x, y), ExactRatio.ZERO, relation,
                String::equals, (one, two) -> true, null);
    }

    /**
     * Two values held to the same ends are not the same values: {@code x == y} with {@code x}
     * between nought and one is false at a half whichever whole number {@code y} is, so a whole
     * {@code y} does not reach every {@code x}, whereas every whole {@code y} is the value of some
     * {@code x}.
     */
    @Test
    void aWholeTermDoesNotTakeEveryValueOfADenseOneWithTheSameEnds() {
        NumericDomain.Bounds unit = dense("0", true, "1", true);
        for (Rel relation : List.of(Rel.EQ, Rel.NE)) {
            assertEquals(Set.of("y"), undivided(denseTerm("x", 1, unit, unit),
                    term("y", -1, unit, unit), relation), relation.toString());
            assertEquals(Set.of("x"), undivided(term("x", 1, unit, unit),
                    denseTerm("y", -1, unit, unit), relation), relation.toString());
            assertEquals(Set.of("x", "y"), undivided(denseTerm("x", 1, unit, unit),
                    denseTerm("y", -1, unit, unit), relation), relation.toString());
            assertEquals(Set.of("x", "y"), undivided(term("x", 1, unit, unit),
                    term("y", -1, unit, unit), relation), relation.toString());
        }
    }

    /** One whole value is a value a whole term takes, and a dense one too. */
    @Test
    void aWholeTermTakesTheOneValueADenseTermIsHeldTo() {
        NumericDomain.Bounds one = dense("1", true, "1", true);
        NumericDomain.Bounds unit = dense("0", true, "1", true);
        assertEquals(Set.of("x"), undivided(denseTerm("x", 1, one, one),
                term("y", -1, unit, unit), Rel.EQ));
    }

    /**
     * {@code x > y} with both above nought and up to one: at the least decimal above nought,
     * {@code y} has no value below {@code x}, so the relation fails there and {@code x} is not
     * left either way for being a dense term whose run is open at nought. Closed at nought, the
     * run holds a value below any {@code x} above it, and the line is at nought.
     */
    @Test
    void aRunOpenAtTheEndTheOtherTermIsHeldToIsNotReachedBeyondIt() {
        NumericDomain.Bounds unit = dense("0", true, "1", true);
        NumericDomain.Bounds aboveNought = dense("0", false, "1", true);
        assertEquals(Set.of(), undivided(denseTerm("x", 1, aboveNought, aboveNought),
                denseTerm("y", -1, aboveNought, aboveNought), Rel.GT));
        assertNull(denseLeavesOf(denseTerm("x", 1, unit, unit),
                denseTerm("y", -1, aboveNought, aboveNought), Rel.GT));
        assertEquals(List.of(line(Rel.LE, 0)), ((Leaves.Settled) denseLeavesOf(
                denseTerm("x", 1, unit, unit), denseTerm("y", -1, unit, unit), Rel.GT)).lines());
    }

    /** {@code x > 0} for {@code x} from the least decimal there is to twice it holds at every
     *  value, whatever the width of the run: nothing is parted. */
    @Test
    void aRunOfTheFinestScaleIsSettledAsAnyOtherIs() {
        NumericDomain.Bounds oneStepToTwo = dense("1E-2147483647", true, "2E-2147483647", true);
        NumericDomain.Bounds nought = dense("0", true, "0", true);
        Leaves.Settled settled = (Leaves.Settled) denseLeavesOf(
                denseTerm("x", 1, oneStepToTwo, oneStepToTwo), denseTerm("y", -1, nought, nought),
                Rel.GT);
        assertEquals(1, settled.runs().size());
        assertEquals(true, settled.runs().getFirst().holds());
        assertEquals(List.of(), settled.lines());
    }

    /**
     * {@code 2x < y} with {@code x} above nought and {@code y} the finest step: the least decimal
     * {@code x} takes is the step, twice it is past {@code y}, and the relation fails at every
     * value. The numbers it holds at, between nought and half a step, are no decimal's, and no run
     * of them is offered.
     */
    @Test
    void aRunBetweenTwoDecimalsHoldsNoneWhenAnEndIsNoDecimal() {
        NumericDomain.Bounds aboveNought = new NumericDomain.Bounds(
                Endpoint.exclusive(Count.of(0)), Endpoint.inclusive(Count.of(1)));
        NumericDomain.Bounds step = dense("1E-2147483647", true, "1E-2147483647", true);
        Leaves.Settled settled = (Leaves.Settled) denseLeavesOf(
                denseTerm("x", 2, aboveNought, aboveNought), denseTerm("y", -1, step, step),
                Rel.LT);
        assertEquals(List.of(), settled.lines());
        assertEquals(List.of(false), settled.runs().stream().map(run -> run.holds()).distinct()
                .toList());
    }

    /**
     * {@code x + 3y < 0} with {@code x} from minus two to minus one and {@code y} from nought to
     * one: it holds at {@code y == 0} and fails at {@code y == 1} whatever {@code x} is, so
     * {@code x} is undivided. The values of {@code y} that are asked of lie from a third to two
     * thirds, which no decimal writes; the decimals just outside them are what {@code y} takes.
     */
    @Test
    void anEndNoDecimalWritesNeedsNoDecimalAtIt() {
        NumericDomain.Bounds x = dense("-2", true, "-1", true);
        NumericDomain.Bounds unit = dense("0", true, "1", true);
        assertEquals(Leaves.Undivided.class, denseLeavesOf(x, unit, unit, 3, Rel.LT).getClass());
    }

    /**
     * {@code 3y > x}: the values of {@code y} that {@code x} needs are a third of {@code x}, which
     * lie on a grid a third of a step fine. At {@code x} one step, {@code 3y} is past it whatever
     * {@code y} is, so {@code x} is not left undivided by {@code y} reaching either side of a third
     * of the step: the grid of the decimals is not the grid of what is needed.
     */
    @Test
    void aWeightThatDividesTheStepSaysNoGridOfTheValuesNeeded() {
        NumericDomain.Bounds step = dense("1E-2147483647", true, "1E-2147483647", true);
        NumericDomain.Bounds upToAStep = dense("0", false, "1E-2147483647", true);
        NumericDomain.Bounds aboveNought = dense("0", false, "1", true);
        NumericDomain.Bounds fromAStep = dense("1E-2147483647", true, "1", true);
        assertEquals(false, undivided(denseTerm("x", -1, upToAStep, upToAStep),
                denseTerm("y", 3, step, step), Rel.GT).contains("x"));
        assertEquals(false, undivided(denseTerm("x", -1, aboveNought, aboveNought),
                denseTerm("y", 3, fromAStep, fromAStep), Rel.GT).contains("x"));
    }

    /**
     * A decimal of a half is a value a whole term cannot take, and a decimal of one is: with
     * {@code x} held to the one decimal and {@code y} whole from nought to one, {@code x == y}
     * is false at a half whatever {@code y} is, and at one it is left either way.
     */
    @Test
    void aWholeTermTakesTheOneDecimalOnlyWhereItIsWhole() {
        NumericDomain.Bounds unit = dense("0", true, "1", true);
        NumericDomain.Bounds half = dense("0.5", true, "0.5", true);
        NumericDomain.Bounds one = dense("1", true, "1", true);
        for (Rel relation : List.of(Rel.EQ, Rel.NE)) {
            assertEquals(false, undivided(denseTerm("x", 1, half, half),
                    term("y", -1, unit, unit), relation).contains("x"), relation.toString());
            assertEquals(true, undivided(denseTerm("x", 1, one, one),
                    term("y", -1, unit, unit), relation).contains("x"), relation.toString());
        }
    }

    /**
     * {@code 3x - y < 0} with {@code y} from nought to one: {@code x} lies below a third wherever
     * {@code y} is, which no decimal writes. The line is at the third all the same, and the
     * values between nought and it are asked of {@code y} as they are.
     */
    @Test
    void anEndNoDecimalWritesIsStillTheEndOfTheRunAskedAbout() {
        NumericDomain.Bounds aboveNought = new NumericDomain.Bounds(
                Endpoint.exclusive(Count.of(0)), null);
        NumericDomain.Bounds unit = dense("0", true, "1", true);
        Leaves leaves = denseLeavesOf(denseTerm("x", 3, aboveNought, aboveNought),
                denseTerm("y", -1, unit, unit), Rel.LT);
        assertEquals(List.of(new Line(Rel.GE, ExactRatio.of(BigInteger.ONE,
                BigInteger.valueOf(3)))), ((Leaves.Settled) leaves).lines());
    }

    /**
     * {@code xy < 1000}, {@code x} from one to five and {@code y} read as though its order ran on:
     * over every {@code x}, {@code y} has to stand from two hundred to a thousand. Counted on an
     * order stopping at a hundred, no {@code y} is there and nothing is shown; on one reaching a
     * thousand, {@code y} leaves every {@code x} either way.
     */
    @Test
    void aFactorPastWhereItsOrderStopsIsNoWitness() {
        NumericDomain.Bounds fromOne = run(1L, 5L);
        for (long stops : new long[] {100, 1000}) {
            var y = new WhatARelationLeavesUndivided.Term<>(List.of("y"), ExactRatio.of(1),
                    NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN, null, true,
                    Granularity.DISCRETE, run(-stops, stops));
            Leaves leaves = WhatARelationLeavesUndivided.leavesOfAProduct(
                    term("x", 1, fromOne, fromOne), y, ExactRatio.of(1000), Rel.LT, true,
                    GREATEST_INT);
            assertEquals(stops == 1000 ? new Leaves.Undivided() : null, leaves,
                    "y counted up to " + stops);
        }
    }

    /**
     * {@code xy = 0}, {@code x} from one to five: only a {@code y} of nought makes it hold, and a
     * {@code y} counted on an order starting at one never is, however its run is read.
     */
    @Test
    void aFactorWhoseOrderHoldsNoNoughtIsNoWitnessOfIt() {
        NumericDomain.Bounds fromOne = run(1L, 5L);
        for (long least : new long[] {1, 0}) {
            var y = new WhatARelationLeavesUndivided.Term<>(List.of("y"), ExactRatio.of(1),
                    NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN, null, true,
                    Granularity.DISCRETE, run(least, 100L));
            Leaves leaves = WhatARelationLeavesUndivided.leavesOfAProduct(
                    term("x", 1, fromOne, fromOne), y, ExactRatio.ZERO, Rel.EQ, true,
                    GREATEST_INT);
            assertEquals(least == 0 ? new Leaves.Undivided() : null, leaves,
                    "y counted from " + least);
        }
    }

    /** A value is taken only on the order it is counted on: a run taken past where the order
     *  stops is no term. */
    @Test
    void aTermTakesNoValuePastItsOrder() {
        assertThrows(IllegalArgumentException.class, () -> new WhatARelationLeavesUndivided.Term<>(
                List.of("y"), ExactRatio.of(1), run(0L, 200L), run(0L, 200L), null, true,
                Granularity.DISCRETE, run(0L, 100L)));
    }

    /**
     * {@code a >= 100 * b}, {@code b} from one: below a hundred it fails whatever {@code b} is,
     * the model's line. Within a hundred of the greatest {@code Int} it holds whatever {@code b}
     * is, because the program works {@code 100 * b} out and a {@code b} past it passes the type: a
     * line of the arithmetic, and none of the model's.
     */
    @Test
    void aValueSettledOnlyBecauseTheOtherWeighedPassesTheTypeIsTheArithmeticsLine() {
        var a = term("a", 1, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN);
        var b = term("b", -100, run(1L, null), run(1L, null));
        Leaves.Settled settled = (Leaves.Settled) WhatARelationLeavesUndivided.leavesOf(
                List.of(a, b), 0, ExactRatio.ZERO, Rel.GE, String::equals,
                (one, other) -> true, Granularity.DISCRETE, GREATEST_INT, List.of(),
                WhatARelationLeavesUndivided.Operations.read(
                        List.of(anIntSum(0, "b", 100)), true));
        long lastWhole = Long.MAX_VALUE / 100 * 100;
        assertEquals(List.of(new Line(Rel.GE, ExactRatio.of(lastWhole))),
                settled.ofTheTypeAlone());
        assertEquals(List.of(new Line(Rel.LE, ExactRatio.of(99))), settled.linesOfTheModel());
    }

    /**
     * The same relation of a program that does not multiply: {@code a / b >= 100} works out no
     * {@code 100 * b}, so a {@code b} past a hundredth of the greatest {@code Int} is a row, and
     * nothing is settled by where the product would stop.
     */
    @Test
    void aValueTheProductWouldStopAtIsNoLineWhereNoProductIsWorkedOut() {
        var a = term("a", 1, NumericDomain.Bounds.OPEN, NumericDomain.Bounds.OPEN);
        var b = term("b", -100, run(1L, null), run(1L, null));
        Leaves leaves = leavesOf(List.of(a, b), 0, 0, Rel.GE);
        assertFalse(leaves instanceof Leaves.Settled settled
                && !settled.ofTheTypeAlone().isEmpty(),
                () -> "a line of the type alone where no product stops: " + leaves);
    }

    /** Runs a point apart are lines apart: a point both leave out is not covered. */
    @Test
    void aPointNoRunTakesIsAGapBetweenTwoDenseRuns() {
        ExactRatio five = ExactRatio.of(5);
        Leaves.Settled apart = new Leaves.Settled(List.of(
                new SettledRun(null, ExactCut.exclusive(five), true),
                new SettledRun(ExactCut.exclusive(five), null, false)), null, null, false,
                List.of(), List.of());
        assertEquals(List.of(new Line(Rel.LT, five), new Line(Rel.GT, five)), apart.lines());
        Leaves.Settled touching = new Leaves.Settled(List.of(
                new SettledRun(null, ExactCut.inclusive(five), true),
                new SettledRun(ExactCut.exclusive(five), null, false)), null, null, false,
                List.of(), List.of());
        assertEquals(List.of(new Line(Rel.LE, five)), touching.lines());
    }
}
