package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.WhatARelationLeavesUndivided.Leaves;
import souther.compiler.inputs.WhatARelationLeavesUndivided.OnTheDifference;
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
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two terms weighed alike or oppositely, over a type that stops at {@code [-5, 4]} and whose
 * arithmetic computes a row only where its positive addends and its negative ones are each no
 * further from nought than four. Every row there is is enumerated, and what is said of the two
 * is what the computed rows say: a value left either way has a computed row on each side, a value
 * settled has none on the other side, and a value the other term has no partner for at the end of
 * the type is the type's and not a line of the model.
 *
 * <p>Three things are kept apart. What the relation reads with the other term open past the ends
 * of the type, what it reads with the other kept inside them, and what a computed row shows. The
 * least value of the type is inside it and is no computed addend, so a sum or a difference that
 * needs it is a row of the type and not one the arithmetic proves.
 */
class TwoTermsWeighedAlikeOrOppositelyAreSettledOnlyWhereTheirComputedRowsSayTest {

    private static final long GREATEST = 4;

    private static final long LEAST = -5;

    private static NumericDomain.Bounds run(Long low, Long high) {
        return new NumericDomain.Bounds(low == null ? null : Endpoint.inclusive(Count.of(low)),
                high == null ? null : Endpoint.inclusive(Count.of(high)));
    }

    private static final NumericDomain.Bounds TYPE = run(LEAST, GREATEST);

    private static final NumericDomain.Bounds OPEN = run(null, null);

    private static final long[][] WEIGHTS = {{1, -1}, {-1, 1}, {1, 1}, {-1, -1}};

    private static final NumericDomain.Bounds[] HELD = {
        TYPE, run(0L, 4L), run(-2L, 2L), run(-5L, 0L)};

    private static final NumericDomain.Bounds[] REACHED = {OPEN, run(0L, 4L), run(-2L, 2L)};

    private static final Rel[] RELATIONS = {Rel.GE, Rel.GT, Rel.LE, Rel.LT, Rel.EQ, Rel.NE};

    private static final long[] CONSTANTS = {-6, -4, -3, -1, 0, 1, 3, 4};

    private static Term<String> term(String place, long weight, NumericDomain.Bounds holds,
                                     NumericDomain.Bounds realizes) {
        return new Term<>(List.of(place), ExactRatio.of(weight), holds, realizes, null, true,
                Granularity.DISCRETE, TYPE);
    }

    private static long endOf(Endpoint end) {
        return ((Count) end.at()).at().longValueExact();
    }

    private static boolean takes(long value, NumericDomain.Bounds bounds) {
        return (bounds.min() == null || endOf(bounds.min()) <= value)
                && (bounds.max() == null || value <= endOf(bounds.max()));
    }

    /** Whether a row of weighed addends is computed: its positive addends together and its
     *  negative ones together are no further from nought than the greatest. */
    private static boolean computes(long... addends) {
        long up = 0;
        long down = 0;
        for (long each : addends) {
            if (each > 0) {
                up += each;
            } else {
                down -= each;
            }
        }
        return up <= GREATEST && down <= GREATEST;
    }

    private static boolean holds(Rel relation, long sum) {
        return relation.holds(Long.signum(sum));
    }

    /** Whether some computed row holds the relation, and whether some computed row fails it, with
     *  the term at {@code at} standing at {@code value} and the other taking {@code reached}. */
    private static boolean[] sidesOf(long[] weights, int at, long value, long constant,
                                     Rel relation, NumericDomain.Bounds reached,
                                     List<OnTheDifference> held) {
        boolean[] sides = new boolean[2];
        for (long other = LEAST; other <= GREATEST; other++) {
            if (!takes(other, reached)) {
                continue;
            }
            long[] at2 = new long[2];
            at2[at] = value;
            at2[1 - at] = other;
            if (!computes(weights[0] * at2[0], weights[1] * at2[1], constant)
                    || !heldBy(held, weights, at2)) {
                continue;
            }
            long sum = weights[0] * at2[0] + weights[1] * at2[1] + constant;
            sides[holds(relation, sum) ? 0 : 1] = true;
        }
        return sides;
    }

    /** Whether every statement of {@code held} holds at the two values, about their sum where
     *  they are weighed alike and their difference where not. */
    private static boolean heldBy(List<OnTheDifference> held, long[] weights, long[] values) {
        for (OnTheDifference each : held) {
            long combined = weights[0] == weights[1] ? values[0] + values[1] : values[0] - values[1];
            long weight = each.weight().floor().orNull().longValue();
            long constant = each.constant().floor().orNull().longValue();
            if (!holds(each.relation(), weight * combined + constant)) {
                return false;
            }
        }
        return true;
    }

    private static boolean within(SettledRun run, long value) {
        ExactRatio at = ExactRatio.of(value);
        return (run.from() == null || at.compareTo(run.from().at()) > 0
                || (run.from().inclusive() && at.compareTo(run.from().at()) == 0))
                && (run.to() == null || at.compareTo(run.to().at()) < 0
                || (run.to().inclusive() && at.compareTo(run.to().at()) == 0));
    }

    private static List<List<OnTheDifference>> heldOptions(long[] weights) {
        long weight = weights[0];
        List<List<OnTheDifference>> out = new ArrayList<>();
        out.add(List.of());
        out.add(List.of(new OnTheDifference(ExactRatio.of(weight), ExactRatio.of(-1), Rel.GE)));
        out.add(List.of(new OnTheDifference(ExactRatio.of(weight), ExactRatio.of(-2), Rel.LE)));
        return out;
    }

    /**
     * What is said of the term at {@code at} is what the computed rows say, for a sum and a
     * difference alike: left either way where a computed row is on each side, settled where none
     * is on the other, and a value only the end of the type keeps from an outcome is the type's.
     */
    @Test
    void whatIsSaidOfTwoTermsIsWhatTheirComputedRowsSay() {
        int said = 0;
        int undivided = 0;
        int ofTheType = 0;
        for (long[] weights : WEIGHTS) {
            for (NumericDomain.Bounds heldA : HELD) {
                for (NumericDomain.Bounds heldB : HELD) {
                    for (NumericDomain.Bounds reached : REACHED) {
                        for (List<OnTheDifference> held : heldOptions(weights)) {
                            for (long constant : CONSTANTS) {
                                for (Rel relation : RELATIONS) {
                                    for (int at = 0; at < 2; at++) {
                                        List<Term<String>> terms = List.of(
                                                term("a", weights[0], heldA, at == 0 ? OPEN : reached),
                                                term("b", weights[1], heldB, at == 0 ? reached : OPEN));
                                        Leaves leaves = WhatARelationLeavesUndivided
                                                .leavesByTheirDifference(terms, at,
                                                        ExactRatio.of(constant), relation, held,
                                                        String::equals,
                                                        BigInteger.valueOf(GREATEST),
                                                        WhatARelationLeavesUndivided
                                                                .Operations.NONE, true);
                                        if (leaves == null) {
                                            continue;
                                        }
                                        said++;
                                        if (leaves instanceof Leaves.Undivided) {
                                            undivided++;
                                        }
                                        if (leaves instanceof Leaves.Settled settled
                                                && !settled.ofTheTypeAlone().isEmpty()) {
                                            ofTheType++;
                                        }
                                        check(leaves, weights, terms, at, constant, relation,
                                                reached, held);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        assertTrue(said > 1000, "some pair is read, or this asks nothing: " + said);
        assertTrue(undivided > 0, "some pair is left either way: " + undivided);
        assertTrue(ofTheType > 0, "some value is the type's alone: " + ofTheType);
    }

    private static void check(Leaves leaves, long[] weights, List<Term<String>> terms, int at,
                              long constant, Rel relation, NumericDomain.Bounds reached,
                              List<OnTheDifference> held) {
        NumericDomain.Bounds mine = terms.get(at).holds();
        String where = leaves + " for weights " + weights[0] + "," + weights[1] + " held "
                + terms.get(0).holds() + " " + terms.get(1).holds() + " reaching " + reached
                + " at " + at + " " + constant + " " + relation + " " + held;
        for (long each = LEAST; each <= GREATEST; each++) {
            long value = each;
            if (!takes(value, mine)) {
                continue;
            }
            boolean[] sides = sidesOf(weights, at, value, constant, relation, reached, held);
            switch (leaves) {
                case Leaves.Undivided _ -> assertTrue(sides[0] && sides[1],
                        "left either way at " + value + ": " + where);
                case Leaves.Settled settled -> {
                    SettledRun inside = settled.runs().stream()
                            .filter(run -> within(run, value)).findFirst().orElse(null);
                    if (inside == null) {
                        if (settled.least() != null && settled.greatest() != null
                                && value >= settled.least().at().floor().orNull().longValue()
                                && value <= settled.greatest().at().floor().orNull().longValue()) {
                            assertTrue(sides[0] && sides[1],
                                    "left either way at " + value + ": " + where);
                        }
                    } else {
                        assertFalse(sides[inside.holds() ? 1 : 0],
                                "settled " + inside.holds() + " at " + value + ": " + where);
                    }
                }
            }
        }
    }

    /**
     * The other term open past the ends of the type, and nothing held of the two: no value has a
     * partner for want of one at the end of the type and draws a line of the model for it.
     */
    @Test
    void anEndOfTheTypeIsNeverALineOfTheModelWhereTheOtherTermIsOpen() {
        for (long[] weights : WEIGHTS) {
            for (long constant : CONSTANTS) {
                for (Rel relation : RELATIONS) {
                    for (int at = 0; at < 2; at++) {
                        List<Term<String>> terms = List.of(term("a", weights[0], TYPE, OPEN),
                                term("b", weights[1], TYPE, OPEN));
                        Leaves leaves = WhatARelationLeavesUndivided.leavesByTheirDifference(
                                terms, at, ExactRatio.of(constant), relation, List.of(),
                                String::equals, BigInteger.valueOf(GREATEST),
                                WhatARelationLeavesUndivided.Operations.NONE, true);
                        if (leaves instanceof Leaves.Settled settled) {
                            assertEquals(List.of(), settled.linesOfTheModel(),
                                    leaves + " for " + weights[0] + "," + weights[1] + " at " + at
                                            + " " + constant + " " + relation);
                        }
                    }
                }
            }
        }
    }

    /**
     * Two values each every value of the type are left either way only where the middle of the
     * type has a computed row on each side. A sum or a difference the middle reaches only by the
     * least value of the type is a row of the type and no computed one.
     */
    @Test
    void twoValuesAreLeftEitherWayOnlyWhereTheMiddleHasAComputedRowOnEachSide() {
        int read = 0;
        for (long[] weights : WEIGHTS) {
            for (long constant : CONSTANTS) {
                for (Rel relation : RELATIONS) {
                    List<Term<String>> terms = List.of(
                            new Term<>(List.of("a"), ExactRatio.of(weights[0]), TYPE, OPEN,
                                    "n", true, Granularity.DISCRETE, TYPE),
                            new Term<>(List.of("b"), ExactRatio.of(weights[1]), TYPE, OPEN,
                                    "n", true, Granularity.DISCRETE, TYPE));
                    Set<String> out = WhatARelationLeavesUndivided.ofTheirDifference(terms,
                            ExactRatio.of(constant), relation, List.of(),
                            new WhatARelationLeavesUndivided.WhereTheRepresentationStops(TYPE),
                            String::equals, BigInteger.valueOf(GREATEST),
                            WhatARelationLeavesUndivided.Operations.NONE, true);
                    if (out.isEmpty()) {
                        continue;
                    }
                    read++;
                    for (long middle : new long[] {-1, 0}) {
                        boolean[] sides = sidesOf(weights, 0, middle, constant, relation, TYPE,
                                List.of());
                        assertTrue(sides[0] && sides[1], "the middle " + middle
                                + " is left either way by a computed row for weights "
                                + weights[0] + "," + weights[1] + " " + constant + " " + relation);
                    }
                }
            }
        }
        assertTrue(read > 0, "some pair is read, or this asks nothing");
    }
}
