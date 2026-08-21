package souther.compiler.numeric;

import java.util.Map;
import java.util.function.Function;

/**
 * What a weighted sum runs between, given what each position in it runs between.
 *
 * <p>Three readers asked this and three answered it. The interval algebra summed a goal's positions
 * to decide whether the goal followed; the reduction summed the rest of a rule to see what it left
 * one position; and the partition layer summed a quantity's positions to decide whether a threshold
 * was a value the quantity ever takes. The arithmetic is four lines and two of them are easy to get
 * wrong in ways nothing catches — so it is written once.
 *
 * <p><b>Which end of a position is read is the coefficient's sign.</b> A position pulling the sum up
 * contributes least at its own least; one pulling it down contributes least at its greatest. Read
 * the same end regardless and the answer is wrong wherever a rule subtracts, which is the error that
 * shows up as a row nobody can build rather than as anything nearer the mistake.
 *
 * <p><b>The sum reaches its end only where every part does.</b> One position that cannot quite reach
 * its own edge is one the sum cannot quite reach either — and an end wrongly called reachable is a
 * point the search is sent to look for and never finds.
 *
 * <p>A {@code null} end is no bound that way. One position unbounded in the direction that matters
 * leaves the whole sum unbounded there, since nothing else can make up for it.
 */
public record Reach(RationalCut least, RationalCut most) {

    /** Bounded at neither end, which is what a sum containing an unbounded position runs between. */
    public static final Reach ANYWHERE = new Reach(null, null);

    public static Reach between(RationalCut least, RationalCut most) {
        return new Reach(least, most);
    }

    /**
     * What {@code Σ coefs·position + constant} runs between.
     *
     * @param positions what each named position runs between; a position it has nothing for runs
     *                  the whole way, which leaves the sum unbounded in whichever directions that
     *                  position could push it
     */
    public static <A> Reach of(Map<A, Rational> coefs, Rational constant,
                               Function<A, Reach> positions) {
        Rational least = constant;
        Rational most = constant;
        boolean leastReached = true;
        boolean mostReached = true;
        for (Map.Entry<A, Rational> each : coefs.entrySet()) {
            Rational weight = each.getValue();
            Reach runs = positions.apply(each.getKey());
            if (runs == null) {
                runs = ANYWHERE;
            }
            RationalCut low = weight.signum() > 0 ? runs.least() : runs.most();
            RationalCut high = weight.signum() > 0 ? runs.most() : runs.least();
            if (least != null && low != null) {
                least = least.plus(weight.times(low.at()));
                leastReached &= low.inclusive();
            } else {
                least = null;
            }
            if (most != null && high != null) {
                most = most.plus(weight.times(high.at()));
                mostReached &= high.inclusive();
            } else {
                most = null;
            }
        }
        return new Reach(least == null ? null : new RationalCut(least, leastReached),
                most == null ? null : new RationalCut(most, mostReached));
    }

    /** Whether either end was found. */
    public boolean saysNothing() {
        return least == null && most == null;
    }
}
