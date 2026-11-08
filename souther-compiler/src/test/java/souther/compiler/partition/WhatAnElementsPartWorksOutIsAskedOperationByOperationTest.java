package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.types.BinOp;
import souther.compiler.types.Type;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * What a step or a closure works out of each element is asked operation by operation, in the
 * order it is written, and not as the number it comes to: {@code acc + p - q} and
 * {@code acc + (p - q)} add the same and stop runs apart.
 *
 * <p>Each answer of {@link AddedOfEachElement#overWholeNumbers} is held to the run itself: every
 * tree of up to three operations over two paths and the answer so far, over small ends of a type,
 * worked out on every row of one element by the rule the run time works it out by. A row of one
 * element stops at an operation of the part only where the total it comes to is past the ends,
 * wherever more than nothing is claimed; and where every row is claimed, no operation stops on any.
 */
class WhatAnElementsPartWorksOutIsAskedOperationByOperationTest {

    private static final BigInteger LEAST = BigInteger.valueOf(-8);
    private static final BigInteger GREATEST = BigInteger.valueOf(7);
    private static final Core P = new Core.Int(0, Type.INT, null);
    private static final Core Q = new Core.Int(1, Type.INT, null);
    private static final List<long[]> RANGES = List.of(
            new long[] {0, 7}, new long[] {-8, 7}, new long[] {-2, 1});
    private static final List<BinOp> OPS = List.of(BinOp.ADD, BinOp.SUB, BinOp.MUL);

    @Test
    void whatIsClaimedHoldsOfEveryRowOfOneElement() {
        int claimed = 0;
        int asked = 0;
        for (AddedOfEachElement.Part part : parts(3)) {
            boolean step = readsTheAnswerSoFar(part);
            AddedOfEachElement each;
            try {
                each = new AddedOfEachElement(part);
            } catch (IllegalArgumentException refused) {
                continue;
            }
            for (long seed : step ? new long[] {0, 2, -3} : new long[] {0}) {
                for (long[] p : RANGES) {
                    for (long[] q : RANGES) {
                        asked++;
                        AddedOfEachElement.Through through = each.overWholeNumbers(
                                BigInteger.valueOf(seed), path -> rangeOf(path, p, q), LEAST,
                                GREATEST);
                        if (through == AddedOfEachElement.Through.NOT_SHOWN) {
                            continue;
                        }
                        claimed++;
                        if (step) {
                            assertNotEquals(AddedOfEachElement.Through.EVERY_ROW, through,
                                    "a walk has running totals: " + part);
                        }
                        heldOfEveryRow(part, seed, p, q, through);
                    }
                }
            }
        }
        // Both answers are asked of a population, and neither is empty.
        assertNotEquals(0, claimed, "something is claimed");
        assertNotEquals(asked, claimed, "something is refused");
    }

    /** The trees of the issue, where the ends a part's operations meet decide the answer. */
    @Test
    void theOrderAPartIsWrittenInDecidesWhatIsShown() {
        AddedOfEachElement.Part p = new AddedOfEachElement.Path(P);
        AddedOfEachElement.Part q = new AddedOfEachElement.Path(Q);
        AddedOfEachElement.Part soFar = new AddedOfEachElement.SoFar();
        AddedOfEachElement.Part difference = worked(BinOp.SUB, p, q);
        long[] noughtOrMore = {0, 7};
        long[] every = {-8, 7};
        // p - q of two numbers at nought or more is within the ends, whatever row it is on.
        assertEquals(AddedOfEachElement.Through.EVERY_ROW,
                through(difference, 0, noughtOrMore, noughtOrMore));
        // Over every number it is past them for some, and the total of one element is it.
        assertEquals(AddedOfEachElement.Through.A_ROW_OF_ONE_ELEMENT,
                through(difference, 0, every, every));
        // acc + (p - q) from two works the difference out first, which gets through.
        assertEquals(AddedOfEachElement.Through.A_ROW_OF_ONE_ELEMENT,
                through(worked(BinOp.ADD, soFar, difference), 2, noughtOrMore, noughtOrMore));
        // acc + p - q from two works out 2 + p first, past the ends where p is seven.
        assertEquals(AddedOfEachElement.Through.NOT_SHOWN,
                through(worked(BinOp.SUB, worked(BinOp.ADD, soFar, p), q), 2, noughtOrMore,
                        noughtOrMore));
        // From nought, the first sum is p, and the difference is the total.
        assertEquals(AddedOfEachElement.Through.A_ROW_OF_ONE_ELEMENT,
                through(worked(BinOp.SUB, worked(BinOp.ADD, soFar, p), q), 0, every, every));
        // acc + (p - q) from two over every number: the difference stops where the total
        // 2 + (p - q) does not.
        assertEquals(AddedOfEachElement.Through.NOT_SHOWN,
                through(worked(BinOp.ADD, soFar, difference), 2, every, every));
    }

    /** The answer so far is read once, along sums from the top, and taken from nothing. */
    @Test
    void theAnswerSoFarIsAddedTo() {
        AddedOfEachElement.Part p = new AddedOfEachElement.Path(P);
        AddedOfEachElement.Part soFar = new AddedOfEachElement.SoFar();
        for (AddedOfEachElement.Part refused : List.of(soFar, worked(BinOp.SUB, p, soFar),
                worked(BinOp.MUL, soFar, p), worked(BinOp.ADD, soFar, soFar),
                worked(BinOp.ADD, p, worked(BinOp.SUB, p, soFar)))) {
            assertThrows(IllegalArgumentException.class, () -> new AddedOfEachElement(refused),
                    refused::toString);
        }
    }

    /** The most paths a product on the way multiplies, which bounds the scale of every
     *  operation of decimals worked out of the element. */
    @Test
    void theFactorsAreTheMostAnyProductMultiplies() {
        AddedOfEachElement.Part p = new AddedOfEachElement.Path(P);
        AddedOfEachElement.Part q = new AddedOfEachElement.Path(Q);
        assertEquals(1, new AddedOfEachElement(p).factors());
        assertEquals(1, new AddedOfEachElement(worked(BinOp.SUB, p, q)).factors());
        assertEquals(2, new AddedOfEachElement(worked(BinOp.ADD, worked(BinOp.MUL, p, q), p))
                .factors());
        assertEquals(3, new AddedOfEachElement(worked(BinOp.MUL, worked(BinOp.MUL, p, q), p))
                .factors());
        assertEquals(2, AddedOfEachElement.ofAJoin().factors());
    }

    private static AddedOfEachElement.Through through(AddedOfEachElement.Part part, long seed,
                                                      long[] p, long[] q) {
        return new AddedOfEachElement(part).overWholeNumbers(BigInteger.valueOf(seed),
                path -> rangeOf(path, p, q), LEAST, GREATEST);
    }

    private static AddedOfEachElement.Part worked(BinOp op, AddedOfEachElement.Part left,
                                                  AddedOfEachElement.Part right) {
        return new AddedOfEachElement.Worked(op, left, right);
    }

    private static FormRange rangeOf(Core path, long[] p, long[] q) {
        long[] ends = path.equals(P) ? p : q;
        return new FormRange(ExactRatio.of(BigInteger.valueOf(ends[0])),
                ExactRatio.of(BigInteger.valueOf(ends[1])));
    }

    /**
     * That {@code through} holds of every row of one element where the paths take a value of
     * {@code p} and of {@code q}: an operation of the part stops the run only where the total is
     * past the ends; and where every row is claimed, no operation of the part stops, on a row of
     * one element or of any number, since none of them reads the answer so far.
     */
    private static void heldOfEveryRow(AddedOfEachElement.Part part, long seed, long[] p,
                                       long[] q, AddedOfEachElement.Through through) {
        for (long pv = p[0]; pv <= p[1]; pv++) {
            for (long qv = q[0]; qv <= q[1]; qv++) {
                Map<Core, Long> values = Map.of(P, pv, Q, qv);
                long total = exactly(part, seed, values);
                boolean totalStops = total < LEAST.longValue() || total > GREATEST.longValue();
                boolean partStops = stops(part, seed, values);
                if (partStops && !totalStops) {
                    fail(through + " for " + part + " from " + seed + " at p=" + pv + " q=" + qv
                            + ": an operation stops where the total " + total + " does not");
                }
                if (through == AddedOfEachElement.Through.EVERY_ROW && partStops) {
                    fail("every row is claimed for " + part + ", and it stops at p=" + pv
                            + " q=" + qv);
                }
            }
        }
    }

    /** What {@code part} comes to on a row of one element, worked out exactly. */
    private static long exactly(AddedOfEachElement.Part part, long seed, Map<Core, Long> values) {
        return switch (part) {
            case AddedOfEachElement.Path(Core read) -> values.get(read);
            case AddedOfEachElement.SoFar _ -> seed;
            case AddedOfEachElement.ReadWithTheTotal _ ->
                    throw new IllegalStateException("not among the trees asked");
            case AddedOfEachElement.Worked(BinOp op, var left, var right) ->
                    apply(op, exactly(left, seed, values), exactly(right, seed, values));
        };
    }

    /** Whether working {@code part} out, operand by operand, meets a number past the ends. */
    private static boolean stops(AddedOfEachElement.Part part, long seed, Map<Core, Long> values) {
        if (!(part instanceof AddedOfEachElement.Worked(BinOp op, var left, var right))) {
            return false;
        }
        if (stops(left, seed, values) || stops(right, seed, values)) {
            return true;
        }
        long value = apply(op, exactly(left, seed, values), exactly(right, seed, values));
        return value < LEAST.longValue() || value > GREATEST.longValue();
    }

    private static long apply(BinOp op, long left, long right) {
        return switch (op) {
            case ADD -> left + right;
            case SUB -> left - right;
            case MUL -> left * right;
            default -> throw new IllegalStateException(op.toString());
        };
    }

    private static boolean readsTheAnswerSoFar(AddedOfEachElement.Part part) {
        return switch (part) {
            case AddedOfEachElement.SoFar _ -> true;
            case AddedOfEachElement.Worked(BinOp _, var left, var right) ->
                    readsTheAnswerSoFar(left) || readsTheAnswerSoFar(right);
            default -> false;
        };
    }

    /** Every tree of at most {@code operations} operations over the two paths and the answer
     *  so far. */
    private static List<AddedOfEachElement.Part> parts(int operations) {
        List<List<AddedOfEachElement.Part>> bySize = new ArrayList<>();
        bySize.add(List.of(new AddedOfEachElement.Path(P), new AddedOfEachElement.Path(Q),
                new AddedOfEachElement.SoFar()));
        for (int n = 1; n <= operations; n++) {
            List<AddedOfEachElement.Part> made = new ArrayList<>();
            for (int left = 0; left < n; left++) {
                for (AddedOfEachElement.Part l : bySize.get(left)) {
                    for (AddedOfEachElement.Part r : bySize.get(n - 1 - left)) {
                        for (BinOp op : OPS) {
                            made.add(new AddedOfEachElement.Worked(op, l, r));
                        }
                    }
                }
            }
            bySize.add(made);
        }
        return bySize.stream().flatMap(List::stream).toList();
    }
}
