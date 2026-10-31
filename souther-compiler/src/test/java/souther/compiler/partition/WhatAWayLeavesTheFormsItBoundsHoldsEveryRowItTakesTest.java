package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.CanonicalForm;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.OrderedRuns;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * What a way is read to leave the forms it bounds ({@link AWayReadForARelation.FormsLeft}) holds
 * every row the way takes, and holds only those where it says it is exact.
 *
 * <p>Asked of ways written at random out of bounds on {@code x}, {@code y} and sums of them, every
 * relation and both ways round, choices nested inside alternatives, and conditions the reading
 * does not read as bounds — a truth, and a bound on an element of a list — and answered by working
 * every condition out at every pair of whole numbers in a square around nought. A way no pair
 * takes is one the reading may say leaves nothing; one a pair takes it never may. Which ways are
 * written is fixed, so a run that goes red goes red again.
 */
class WhatAWayLeavesTheFormsItBoundsHoldsEveryRowItTakesTest {

    private static final int REACH = 5;
    private static final int WAYS = 600;

    /** A condition, and whether a pair of values of {@code x} and {@code y} meets it. */
    private sealed interface Asked {

        OnTheWay written();

        boolean heldAt(int x, int y);
    }

    /** {@code onX * x + onY * y rel threshold}. */
    private record Bound(int onX, int onY, Rel rel, int threshold, OnTheWay written)
            implements Asked {

        @Override
        public boolean heldAt(int x, int y) {
            return rel.holds(Integer.signum(onX * x + onY * y - threshold));
        }
    }

    /** A condition the reading reads as no bound, which some value of what it asks of meets
     *  beside any pair. */
    private record NotABound(OnTheWay written) implements Asked {

        @Override
        public boolean heldAt(int x, int y) {
            return true;
        }
    }

    /** A choice, met where every condition of one of its alternatives is. */
    private record Choice(List<List<Asked>> alternatives, OnTheWay written) implements Asked {

        @Override
        public boolean heldAt(int x, int y) {
            return alternatives.stream().anyMatch(each -> heldAll(each, x, y));
        }
    }

    private static boolean heldAll(List<Asked> asked, int x, int y) {
        return asked.stream().allMatch(each -> each.heldAt(x, y));
    }

    private static final class Writing {

        private final Random random = new Random(2918);
        private int choices = 1;

        List<Asked> way(int depth) {
            List<Asked> out = new ArrayList<>();
            for (int each = 1 + random.nextInt(3); each > 0; each--) {
                out.add(condition(depth));
            }
            return out;
        }

        private Asked condition(int depth) {
            int which = random.nextInt(20);
            if (which < 3) {
                return new NotABound(WaysReadAgain.truth("t", random.nextBoolean()));
            }
            if (which < 5) {
                return new NotABound(WaysReadAgain.anElement(1, Rel.LT, random.nextInt(3)));
            }
            if (which < 10 && depth < 2) {
                List<List<Asked>> alternatives = new ArrayList<>();
                List<List<OnTheWay>> written = new ArrayList<>();
                for (int each = 2 + random.nextInt(2); each > 0; each--) {
                    List<Asked> alternative = way(depth + 1);
                    alternatives.add(alternative);
                    written.add(alternative.stream().map(Asked::written).toList());
                }
                return new Choice(alternatives, WaysReadAgain.oneOf(choices++, written));
            }
            int onX = random.nextInt(5) - 2;
            int onY = onX == 0 ? 1 + random.nextInt(2) : random.nextInt(3) - 1;
            Rel rel = Rel.values()[random.nextInt(Rel.values().length)];
            int threshold = random.nextInt(7) - 3;
            return new Bound(onX, onY, rel, threshold,
                    WaysReadAgain.weighed(onX, onY, rel, threshold));
        }
    }

    /** Whether every form {@code left} bounds has its value at {@code x} and {@code y} in the
     *  runs it leaves it. */
    private static boolean leftAt(AWayReadForARelation.FormsLeft left, int x, int y) {
        for (Map.Entry<CanonicalForm<NumericTerm>, OrderedRuns> each : left.runs().entrySet()) {
            ExactRatio value = ExactRatio.ZERO;
            for (Map.Entry<NumericTerm, ExactRatio> weighed : each.getKey().coefs().entrySet()) {
                int at;
                if (weighed.getKey().equals(new NumericTerm.ValueOf(WaysReadAgain.X))) {
                    at = x;
                } else if (weighed.getKey().equals(new NumericTerm.ValueOf(WaysReadAgain.Y))) {
                    at = y;
                } else {
                    fail("a bound on what is no one value was read as one: " + weighed.getKey());
                    return false;
                }
                value = value.plus(ExactRatio.of(at).times(weighed.getValue())
                        .orFail("a small weight times a small number"))
                        .orFail("a sum of small numbers");
            }
            if (!(Count.written(value) instanceof ExactAnswer.Held<Optional<Count>>(
                    Optional<Count> place)) || place.isEmpty()) {
                fail("a whole number is a count: " + value);
                return false;
            }
            if (!each.getValue().admits(place.get())) {
                return false;
            }
        }
        return true;
    }

    @Test
    void everyRowAWayTakesIsLeftAndOnlyThoseWhereTheReadingIsExact() {
        Writing writing = new Writing();
        int exact = 0;
        int nothing = 0;
        for (int way = 0; way < WAYS; way++) {
            List<Asked> asked = writing.way(0);
            AWayReadForARelation.FormsLeft left = new AWayReadForARelation.FormsRead()
                    .of(asked.stream().map(Asked::written).toList());
            exact += left.exact() ? 1 : 0;
            nothing += left.holdsNothing() ? 1 : 0;
            for (int x = -REACH; x <= REACH; x++) {
                for (int y = -REACH; y <= REACH; y++) {
                    boolean held = heldAll(asked, x, y);
                    boolean leftHere = leftAt(left, x, y);
                    if (held && !leftHere) {
                        fail("the way is taken at x = " + x + ", y = " + y
                                + " and the reading leaves it out: " + asked + " read as " + left);
                    }
                    if (left.exact() && leftHere && !held) {
                        fail("the reading says it is exact and leaves x = " + x + ", y = " + y
                                + ", which the way is not taken at: " + asked + " read as "
                                + left);
                    }
                }
            }
        }
        int readExactly = exact;
        int readAsNone = nothing;
        assertTrue(readExactly > 0 && readAsNone > 0,
                () -> "the ways written are some the reading says it is exact of, and some it"
                        + " says no row takes: " + readExactly + " and " + readAsNone);
    }
}
