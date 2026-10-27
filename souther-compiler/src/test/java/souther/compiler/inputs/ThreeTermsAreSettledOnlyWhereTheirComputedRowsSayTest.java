package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.WhatARelationLeavesUndivided.Leaves;
import souther.compiler.inputs.WhatARelationLeavesUndivided.SettledRun;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Term;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Three or more terms, over a type that stops at {@code [-5, 4]} and whose arithmetic computes a
 * row only where its positive addends and its negative ones are each no further from nought than
 * four. Every row there is is enumerated, and what is said of the term asked of is what the
 * computed rows say: a value left either way has a computed row on each side or none that the
 * size alone keeps from one, a value settled has none on the other, and a value that only the
 * size the arithmetic stops at leaves is the type's and not a line of the model.
 *
 * <p>The terms may be weighed by a share, as the terms of a sum divided by a number are, which
 * changes neither the numbers added up nor the side a sum comes out on.
 *
 * <p>With the greatest value at four, {@code a + b + c >= 3} at {@code a} equal to four holds in
 * every row whose sum is computed with the three added up, and fails in one whose sum is computed
 * and compared with three. The relation does not say which it is, so no value at an end is settled
 * for want of a row: it is left undivided where the model draws no line there.
 */
class ThreeTermsAreSettledOnlyWhereTheirComputedRowsSayTest {

    private static final long GREATEST = 4;

    private static final long LEAST = -5;

    /** How far past the type's ends a term is let run where the arithmetic is let go. */
    private static final long FAR = 12;

    private static NumericDomain.Bounds run(long low, long high) {
        return new NumericDomain.Bounds(Endpoint.inclusive(Count.of(low)),
                Endpoint.inclusive(Count.of(high)));
    }

    private static final NumericDomain.Bounds TYPE = run(LEAST, GREATEST);

    private static final NumericDomain.Bounds OPEN = new NumericDomain.Bounds(null, null);

    /** What the others are held to, and what they are shown to take within that. */
    private record Other(NumericDomain.Bounds holds, NumericDomain.Bounds realizes) {}

    private static final List<Other> OTHERS = List.of(
            new Other(OPEN, OPEN),
            new Other(OPEN, run(0, 4)),
            new Other(OPEN, run(-2, 2)),
            new Other(run(0, 4), run(0, 4)),
            new Other(run(-2, 2), run(-2, 2)),
            new Other(run(-5, 0), run(-5, 0)));

    private static final NumericDomain.Bounds[] HELD_AT = {OPEN, run(0, 4), run(-2, 2)};

    private static final long[][] WEIGHTS = {
        {1, 1, 1}, {1, 1, -1}, {1, -1, -1}, {-1, -1, -1}, {2, 1, 1}, {1, 1, 1, 1}, {1, 1, -1, -1}};

    private static final Rel[] RELATIONS = {Rel.GE, Rel.GT, Rel.LE, Rel.LT, Rel.EQ, Rel.NE};

    private static final long[] CONSTANTS = {-7, -4, -3, -1, 0, 1, 3, 4, 6};

    /** The term weighed {@code weight} over {@code divisor}: a sum divided by a number is the
     *  sum's terms each weighed by its share. */
    private static Term<String> term(String place, long weight, long divisor,
                                     NumericDomain.Bounds holds, NumericDomain.Bounds realizes) {
        return new Term<>(List.of(place),
                ExactRatio.of(weight).dividedBy(ExactRatio.of(divisor)).orNull(), holds, realizes,
                null, true, Granularity.DISCRETE, TYPE);
    }

    private static long endOf(Endpoint end) {
        return ((Count) end.at()).at().longValueExact();
    }

    private static boolean takes(long value, NumericDomain.Bounds bounds) {
        return (bounds.min() == null || endOf(bounds.min()) <= value)
                && (bounds.max() == null || value <= endOf(bounds.max()));
    }

    private static boolean computes(long constant, long[] addends) {
        long up = Math.max(constant, 0);
        long down = Math.max(-constant, 0);
        for (long each : addends) {
            up += Math.max(each, 0);
            down += Math.max(-each, 0);
        }
        return up <= GREATEST && down <= GREATEST;
    }

    /**
     * Whether some row holds the relation and whether some row fails it, with the term at
     * {@code at} at {@code value}, each other term over the values of {@code ranges} that the type
     * holds, and the arithmetic stopping at the greatest only where {@code computed}.
     */
    private static boolean[] sidesOf(long[] weights, int at, long value, long constant,
                                     Rel relation, List<NumericDomain.Bounds> ranges,
                                     Rows rows) {
        boolean[] sides = new boolean[2];
        long[] values = new long[weights.length];
        values[at] = value;
        walk(weights, at, 0, values, constant, relation, ranges, rows, sides);
        return sides;
    }

    /**
     * Which rows are computed. The relation holds a sum against a constant, and whether the
     * constant is one of the numbers the program adds up, as in {@code a + b + c - 100 >= 0}, or
     * the sum is computed and only compared with it, as in {@code a + b + c >= 100}, is not in the
     * relation. A claim that no row stands on a side has to hold either way.
     */
    private enum Rows {
        /** The arithmetic does not stop. */
        LET_GO,
        /** The constant is added up with the numbers. */
        WITH_THE_CONSTANT,
        /** The numbers are added up and the sum compared with the constant. */
        WITHOUT_THE_CONSTANT
    }

    private static void walk(long[] weights, int at, int next, long[] values, long constant,
                             Rel relation, List<NumericDomain.Bounds> ranges, Rows rows,
                             boolean[] sides) {
        if (next == weights.length) {
            long[] weighed = new long[weights.length];
            long sum = constant;
            for (int i = 0; i < weights.length; i++) {
                weighed[i] = weights[i] * values[i];
                sum += weighed[i];
            }
            if (rows == Rows.LET_GO
                    || computes(rows == Rows.WITH_THE_CONSTANT ? constant : 0, weighed)) {
                sides[relation.holds(Long.signum(sum)) ? 0 : 1] = true;
            }
            return;
        }
        if (next == at) {
            walk(weights, at, next + 1, values, constant, relation, ranges, rows, sides);
            return;
        }
        NumericDomain.Bounds range = ranges.get(next);
        for (long each = -FAR; each <= FAR; each++) {
            if (takes(each, range)
                    && (rows == Rows.LET_GO || (each >= LEAST && each <= GREATEST))) {
                values[next] = each;
                walk(weights, at, next + 1, values, constant, relation, ranges, rows, sides);
            }
        }
    }

    private static boolean within(SettledRun run, long value) {
        ExactRatio at = ExactRatio.of(value);
        return (run.from() == null || at.compareTo(run.from().at()) > 0
                || (run.from().inclusive() && at.compareTo(run.from().at()) == 0))
                && (run.to() == null || at.compareTo(run.to().at()) < 0
                || (run.to().inclusive() && at.compareTo(run.to().at()) == 0));
    }

    private record Case(long[] weights, long divisor, NumericDomain.Bounds heldAt, Other other,
                        long constant, Rel relation, int at) {

        @Override
        public String toString() {
            return "weights " + java.util.Arrays.toString(weights) + " over " + divisor + " held "
                    + heldAt
                    + " others " + other + " " + constant + " " + relation + " at " + at;
        }

        List<Term<String>> terms() {
            List<Term<String>> out = new ArrayList<>();
            for (int i = 0; i < weights.length; i++) {
                out.add(i == at ? term("t" + i, weights[i], divisor, heldAt, OPEN)
                        : term("t" + i, weights[i], divisor, other.holds(), other.realizes()));
            }
            return out;
        }

        Leaves leaves() {
            return WhatARelationLeavesUndivided.leavesOf(terms(), at,
                    ExactRatio.of(constant).dividedBy(ExactRatio.of(divisor)).orNull(),
                    relation, String::equals, (one, two) -> true, Granularity.DISCRETE,
                    BigInteger.valueOf(GREATEST));
        }

        /** The ranges each term other than the one at {@code at} is let take, by what it holds
         *  within the type. */
        List<NumericDomain.Bounds> held() {
            List<NumericDomain.Bounds> out = new ArrayList<>();
            for (int i = 0; i < weights.length; i++) {
                out.add(other.holds());
            }
            return out;
        }

        /** The same by what the others are shown to take, within the type. */
        List<NumericDomain.Bounds> shown() {
            List<NumericDomain.Bounds> out = new ArrayList<>();
            for (int i = 0; i < weights.length; i++) {
                out.add(other.realizes().min() == null && other.realizes().max() == null
                        ? TYPE : other.realizes());
            }
            return out;
        }

        /** The same with every other let run far past the type where it is shown to take all of
         *  it. */
        List<NumericDomain.Bounds> letGo() {
            List<NumericDomain.Bounds> out = new ArrayList<>();
            for (int i = 0; i < weights.length; i++) {
                out.add(other.realizes().equals(OPEN) ? run(-FAR, FAR) : other.realizes());
            }
            return out;
        }
    }

    private static List<Case> everyCase() {
        List<Case> out = new ArrayList<>();
        for (long[] weights : WEIGHTS) {
            // An average: the numbers added up, and the sum divided by a number.
            boolean added = java.util.Arrays.stream(weights).allMatch(weight -> weight == 1);
            for (long divisor : added ? new long[] {1, 3} : new long[] {1}) {
                for (NumericDomain.Bounds heldAt : HELD_AT) {
                    for (Other other : OTHERS) {
                        for (long constant : CONSTANTS) {
                            for (Rel relation : RELATIONS) {
                                for (int at = 0; at < weights.length; at++) {
                                    out.add(new Case(weights, divisor, heldAt, other, constant,
                                            relation, at));
                                }
                            }
                        }
                    }
                }
            }
        }
        return out;
    }

    /**
     * What is said of the term at {@code at} is what the computed rows say: settled where no
     * computed row is on the other side, and left either way only where a computed row is on each
     * side or the size the arithmetic stops at alone keeps one from it. Left undivided is no claim
     * that every value has a row on each side: the ends of the type are read as the class's account
     * reads them.
     */
    @Test
    void whatIsSaidOfSeveralTermsIsWhatTheirComputedRowsSay() {
        int said = 0;
        int undivided = 0;
        int ofTheType = 0;
        for (Case each : everyCase()) {
            Leaves leaves = each.leaves();
            if (leaves == null) {
                continue;
            }
            said++;
            if (leaves instanceof Leaves.Undivided) {
                undivided++;
            }
            if (leaves instanceof Leaves.Settled settled && !settled.ofTheTypeAlone().isEmpty()) {
                ofTheType++;
            }
            long[] weights = each.weights();
            // The least value of the type is no computed addend, so no computed row stands at it.
            for (long value = LEAST + 1; value <= GREATEST; value++) {
                if (!takes(value, each.heldAt())) {
                    continue;
                }
                boolean[] possible = sidesOf(weights, each.at(), value, each.constant(),
                        each.relation(), each.held(), Rows.WITH_THE_CONSTANT);
                boolean[] shown = sidesOf(weights, each.at(), value, each.constant(),
                        each.relation(), each.shown(), Rows.WITH_THE_CONSTANT);
                boolean[] letGo = sidesOf(weights, each.at(), value, each.constant(),
                        each.relation(), each.letGo(), Rows.LET_GO);
                boolean eitherWay = (shown[0] && shown[1]) || (letGo[0] && letGo[1]);
                switch (leaves) {
                    case Leaves.Undivided _ -> assertTrue(eitherWay,
                            "left either way at " + value + ": " + each);
                    case Leaves.Settled settled -> {
                        long at = value;
                        SettledRun inside = settled.runs().stream()
                                .filter(run -> within(run, at)).findFirst().orElse(null);
                        if (inside != null) {
                            assertFalse(possible[inside.holds() ? 1 : 0],
                                    "settled " + inside.holds() + " at " + value + ": " + each
                                            + " " + leaves);
                        } else if (settled.least() != null && settled.greatest() != null
                                && value >= settled.least().at().floor().orNull().longValue()
                                && value <= settled.greatest().at().floor().orNull().longValue()) {
                            assertTrue(eitherWay,
                                    "left either way at " + value + ": " + each + " " + leaves);
                        }
                    }
                }
            }
        }
        assertTrue(said > 1000, "some term is read, or this asks nothing: " + said);
        assertTrue(undivided > 0, "some term is left either way: " + undivided);
        assertTrue(ofTheType > 0, "some value is the type's alone: " + ofTheType);
    }

    /**
     * A line the model does not draw is one the arithmetic's size alone draws: with nothing held
     * of the others but the type and the arithmetic let go, every value of the term has a row on
     * each side. So where the others are held to nothing, a value settled with no line of the
     * model's is never one a term's own range or a statement settles.
     */
    @Test
    void aValueTheModelDrawsNoLineForIsOneTheSizeAloneSettles() {
        int ofTheType = 0;
        for (Case each : everyCase()) {
            if (!each.other().holds().equals(OPEN) || !each.other().realizes().equals(OPEN)
                    || !each.heldAt().equals(OPEN)
                    || !(each.leaves() instanceof Leaves.Settled settled)
                    || settled.ofTheTypeAlone().isEmpty()
                    || !settled.linesOfTheModel().isEmpty()) {
                continue;
            }
            ofTheType++;
            for (long value = LEAST + 1; value <= GREATEST; value++) {
                boolean[] letGo = sidesOf(each.weights(), each.at(), value, each.constant(),
                        each.relation(), each.letGo(), Rows.LET_GO);
                assertTrue(letGo[0] && letGo[1], "a line of the model at " + value + ": " + each
                        + " " + settled);
            }
        }
        assertTrue(ofTheType > 0, "some value is the type's alone: " + ofTheType);
    }

    /**
     * Three numbers of the type, each open, held against a constant: no line of the model is
     * drawn on any of them, so each place is left undivided, and nothing is said of the side a row
     * stands on at the greatest value of one of them.
     *
     * <p>At the greatest, {@code a + b + c >= 3} fails in a row of {@code b} at {@code -2} where
     * the sum is computed and compared with three, and in none where three is added up with the
     * numbers. Which it is the relation does not say, so it settles that value neither way.
     */
    @Test
    void theGreatestValueOfOneOfThreeOpenTermsDrawsNoLineAndIsSettledNeitherWay() {
        for (int at = 0; at < 3; at++) {
            Case each = new Case(new long[] {1, 1, 1}, 1, OPEN, OTHERS.getFirst(), -3, Rel.GE,
                    at);
            Leaves leaves = each.leaves();
            assertNotNull(leaves, "something is said of " + each);
            if (leaves instanceof Leaves.Settled settled) {
                assertEquals(List.of(), settled.linesOfTheModel(), "no line of the model");
                assertTrue(settled.leavesItsPlacesUndivided(null), "the place is left undivided");
                assertTrue(settled.runs().stream().noneMatch(run -> within(run, GREATEST)),
                        "the greatest is settled neither way: " + settled);
            }
            boolean[] summed = sidesOf(each.weights(), at, GREATEST, -3, Rel.GE, each.held(),
                    Rows.WITHOUT_THE_CONSTANT);
            assertTrue(summed[0] && summed[1], "a row on each side where the sum is compared");
        }
    }
}
