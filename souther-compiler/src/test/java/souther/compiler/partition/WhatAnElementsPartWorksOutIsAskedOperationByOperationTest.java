package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
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
 * <p>Each answer of {@link AddedOfEachElement#overWholeNumbers} is held to the run itself: trees
 * over two paths, a number written out, the answer so far and a name given the value of a tree,
 * over small ends of a type, worked out on every row of one element by the rule the run time
 * works it out by — every name's value first, read or not, then the answer. A row of one element
 * stops at an operation of the step only where the total it comes to is past the ends, wherever
 * more than nothing is claimed. Where every row is claimed, no operation of a closure stops on
 * any, and a walk stops on a row of two elements only where its answer is past the ends.
 */
class WhatAnElementsPartWorksOutIsAskedOperationByOperationTest {

    private static final BigInteger LEAST = BigInteger.valueOf(-4);
    private static final BigInteger GREATEST = BigInteger.valueOf(3);
    private static final Core P = new Core.Int(0, Type.INT, null);
    private static final Core Q = new Core.Int(1, Type.INT, null);
    private static final AddedOfEachElement.Part PATH_P = new AddedOfEachElement.Path(P);
    private static final AddedOfEachElement.Part PATH_Q = new AddedOfEachElement.Path(Q);
    private static final AddedOfEachElement.Part SO_FAR = new AddedOfEachElement.SoFar();
    private static final AddedOfEachElement.Part THREE =
            new AddedOfEachElement.Written(BigDecimal.valueOf(3));
    private static final AddedOfEachElement.Part NOUGHT =
            new AddedOfEachElement.Written(BigDecimal.ZERO);
    private static final BindingId D = new BindingId(new BindingOwner.OfValue("w1", "m"), 0);
    private static final AddedOfEachElement.Part NAMED_D = new AddedOfEachElement.Named(D);
    private static final List<long[]> RANGES = List.of(
            new long[] {0, 3}, new long[] {-4, 3}, new long[] {-1, 1});
    private static final List<BinOp> OPS = List.of(BinOp.ADD, BinOp.SUB, BinOp.MUL);

    @Test
    void whatIsClaimedHoldsOfEveryRowOfOneElement() {
        int claimed = 0;
        int asked = 0;
        for (AddedOfEachElement each : steps()) {
            boolean step = readsTheAnswerSoFar(each.answer());
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
                        heldOfEveryRow(each, seed, p, q, through);
                        if (step && through == AddedOfEachElement.Through.EVERY_ROW) {
                            heldOfEveryRowOfTwo(each, seed, p, q);
                        }
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
        AddedOfEachElement.Part difference = worked(BinOp.SUB, PATH_P, PATH_Q);
        long[] noughtOrMore = {0, 3};
        long[] every = {-4, 3};
        // p - q of two numbers at nought or more is within the ends, whatever row it is on.
        assertEquals(AddedOfEachElement.Through.EVERY_ROW,
                through(difference, 0, noughtOrMore, noughtOrMore));
        // Over every number it is past them for some, and the total of one element is it.
        assertEquals(AddedOfEachElement.Through.A_ROW_OF_ONE_ELEMENT,
                through(difference, 0, every, every));
        // acc + (p - q) from two works the difference out first, which gets through.
        assertEquals(AddedOfEachElement.Through.A_ROW_OF_ONE_ELEMENT,
                through(worked(BinOp.ADD, SO_FAR, difference), 2, noughtOrMore, noughtOrMore));
        // acc + p - q from two works out 2 + p first, past the ends where p is two or more.
        assertEquals(AddedOfEachElement.Through.NOT_SHOWN,
                through(worked(BinOp.SUB, worked(BinOp.ADD, SO_FAR, PATH_P), PATH_Q), 2,
                        noughtOrMore, noughtOrMore));
        // From nought, the first sum is p, and the difference is the total.
        assertEquals(AddedOfEachElement.Through.A_ROW_OF_ONE_ELEMENT,
                through(worked(BinOp.SUB, worked(BinOp.ADD, SO_FAR, PATH_P), PATH_Q), 0, every,
                        every));
        // acc + (p - q) from two over every number: the difference stops where the total
        // 2 + (p - q) does not.
        assertEquals(AddedOfEachElement.Through.NOT_SHOWN,
                through(worked(BinOp.ADD, SO_FAR, difference), 2, every, every));
        // A name given p + 3 is worked out though nothing reads it, and passes the ends where
        // p is past nought.
        AddedOfEachElement unread = new AddedOfEachElement(
                List.of(new AddedOfEachElement.Bound(D, worked(BinOp.ADD, PATH_P, THREE))),
                Map.of(), PATH_Q);
        assertEquals(AddedOfEachElement.Through.NOT_SHOWN, unread.overWholeNumbers(
                BigInteger.ZERO, path -> rangeOf(path, noughtOrMore, noughtOrMore), LEAST,
                GREATEST));
    }

    /** The answer so far is read once, along sums from the top, taken from nothing, and given to
     *  no name. */
    @Test
    void theAnswerSoFarIsAddedTo() {
        for (AddedOfEachElement.Part refused : List.of(SO_FAR, worked(BinOp.SUB, PATH_P, SO_FAR),
                worked(BinOp.MUL, SO_FAR, PATH_P), worked(BinOp.ADD, SO_FAR, SO_FAR),
                worked(BinOp.ADD, PATH_P, worked(BinOp.SUB, PATH_P, SO_FAR)))) {
            assertThrows(IllegalArgumentException.class, () -> new AddedOfEachElement(refused),
                    refused::toString);
        }
        assertThrows(IllegalArgumentException.class, () -> new AddedOfEachElement(
                List.of(new AddedOfEachElement.Bound(D, worked(BinOp.ADD, SO_FAR, PATH_P))),
                Map.of(), NAMED_D));
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
     * {@code p} and of {@code q}: an operation of the step stops the run only where the total is
     * past the ends; and where every row is claimed of a closure, no operation stops, on a row of
     * one element or of any number, since none of them reads the answer so far.
     */
    private static void heldOfEveryRow(AddedOfEachElement each, long seed, long[] p, long[] q,
                                       AddedOfEachElement.Through through) {
        for (long pv = p[0]; pv <= p[1]; pv++) {
            for (long qv = q[0]; qv <= q[1]; qv++) {
                Map<Core, Long> values = Map.of(P, pv, Q, qv);
                Map<BindingId, Long> named = new HashMap<>();
                boolean[] stops = {false};
                for (AddedOfEachElement.Bound bound : each.bound()) {
                    named.put(bound.name(), workedOut(bound.value(), seed, values, named, stops));
                }
                long total = workedOut(each.answer(), seed, values, named, stops);
                boolean totalStops = total < LEAST.longValue() || total > GREATEST.longValue();
                if (stops[0] && !totalStops) {
                    fail(through + " for " + each + " from " + seed + " at p=" + pv + " q=" + qv
                            + ": an operation stops where the total " + total + " does not");
                }
                if (through == AddedOfEachElement.Through.EVERY_ROW && stops[0]
                        && !readsTheAnswerSoFar(each.answer())) {
                    fail("every row is claimed for " + each + ", and it stops at p=" + pv
                            + " q=" + qv);
                }
            }
        }
    }

    /**
     * That a walk claimed on every row gets through on every row of two elements whose answer is
     * within the ends: the answer so far after the first element is the seed for the second, and
     * no operation of either step stops where the answer does not.
     */
    private static void heldOfEveryRowOfTwo(AddedOfEachElement each, long seed, long[] p,
                                            long[] q) {
        for (long p1 = p[0]; p1 <= p[1]; p1++) {
            for (long q1 = q[0]; q1 <= q[1]; q1++) {
                boolean[] stops = {false};
                long between = stepOf(each, seed, Map.of(P, p1, Q, q1), stops);
                for (long p2 = p[0]; p2 <= p[1]; p2++) {
                    for (long q2 = q[0]; q2 <= q[1]; q2++) {
                        boolean[] after = {stops[0]};
                        long total = stepOf(each, between, Map.of(P, p2, Q, q2), after);
                        if (after[0] && total >= LEAST.longValue()
                                && total <= GREATEST.longValue()) {
                            fail("every row is claimed for " + each + " from " + seed
                                    + ", and a row of (" + p1 + ", " + q1 + "), (" + p2 + ", "
                                    + q2 + ") stops where its answer " + total + " does not");
                        }
                    }
                }
            }
        }
    }

    /** One step of {@code each} from {@code soFar} over an element with {@code values}. */
    private static long stepOf(AddedOfEachElement each, long soFar, Map<Core, Long> values,
                               boolean[] stops) {
        Map<BindingId, Long> named = new HashMap<>();
        for (AddedOfEachElement.Bound bound : each.bound()) {
            named.put(bound.name(), workedOut(bound.value(), soFar, values, named, stops));
        }
        return workedOut(each.answer(), soFar, values, named, stops);
    }

    /**
     * What {@code part} comes to on a row of one element, worked out exactly, operand by operand;
     * {@code stops} is set where an operation meets a number past the ends. A name read works
     * out nothing again.
     */
    private static long workedOut(AddedOfEachElement.Part part, long seed, Map<Core, Long> values,
                                  Map<BindingId, Long> named, boolean[] stops) {
        return switch (part) {
            case AddedOfEachElement.Path(Core read) -> values.get(read);
            case AddedOfEachElement.Written(BigDecimal value) -> value.longValueExact();
            case AddedOfEachElement.Named(BindingId name) -> named.get(name);
            case AddedOfEachElement.SoFar _ -> seed;
            case AddedOfEachElement.ReadWithTheTotal _ ->
                    throw new IllegalStateException("not among the trees asked");
            case AddedOfEachElement.Worked(BinOp op, var left, var right) -> {
                long value = apply(op, workedOut(left, seed, values, named, stops),
                        workedOut(right, seed, values, named, stops));
                stops[0] |= value < LEAST.longValue() || value > GREATEST.longValue();
                yield value;
            }
        };
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

    /**
     * The steps asked: every tree of at most three operations over the two paths and the answer
     * so far; every one of at most two that also writes a number out; and, for each tree of at
     * most two operations of the paths and that number, a name given it and read as the whole
     * answer, beside the answer so far, beside a path, or not at all. Those the record refuses
     * are no step there is.
     */
    private static List<AddedOfEachElement> steps() {
        List<AddedOfEachElement> out = new ArrayList<>();
        for (AddedOfEachElement.Part part : parts(3, List.of(PATH_P, PATH_Q, SO_FAR))) {
            addIfAStep(out, List.of(), part);
        }
        for (AddedOfEachElement.Part part : parts(2, List.of(PATH_P, PATH_Q, SO_FAR, THREE))) {
            addIfAStep(out, List.of(), part);
        }
        // A negation is held as nought less the number, and asked as any difference is.
        for (AddedOfEachElement.Part part : parts(1, List.of(PATH_P, PATH_Q, SO_FAR))) {
            addIfAStep(out, List.of(), worked(BinOp.SUB, NOUGHT, part));
            addIfAStep(out, List.of(), worked(BinOp.ADD, SO_FAR, worked(BinOp.SUB, NOUGHT, part)));
        }
        for (AddedOfEachElement.Part value : parts(2, List.of(PATH_P, PATH_Q, THREE))) {
            List<AddedOfEachElement.Bound> bound = List.of(new AddedOfEachElement.Bound(D, value));
            for (AddedOfEachElement.Part answer : List.of(NAMED_D,
                    worked(BinOp.ADD, SO_FAR, NAMED_D), worked(BinOp.ADD, NAMED_D, SO_FAR),
                    worked(BinOp.SUB, SO_FAR, NAMED_D), worked(BinOp.ADD, NAMED_D, PATH_P),
                    PATH_P, worked(BinOp.ADD, SO_FAR, PATH_P))) {
                addIfAStep(out, bound, answer);
            }
        }
        return out;
    }

    private static void addIfAStep(List<AddedOfEachElement> out,
                                   List<AddedOfEachElement.Bound> bound,
                                   AddedOfEachElement.Part answer) {
        try {
            out.add(new AddedOfEachElement(bound, Map.of(), answer));
        } catch (IllegalArgumentException refused) {
            // No step is written so.
        }
    }

    /** Every tree of at most {@code operations} operations over {@code leaves}. */
    private static List<AddedOfEachElement.Part> parts(int operations,
                                                       List<AddedOfEachElement.Part> leaves) {
        List<List<AddedOfEachElement.Part>> bySize = new ArrayList<>();
        bySize.add(leaves);
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
