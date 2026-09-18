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
public record Reach(ExactCut least, ExactCut most) {

    /** Bounded at neither end, which is what a sum containing an unbounded position runs between. */
    public static final Reach ANYWHERE = new Reach(null, null);

    public static Reach between(ExactCut least, ExactCut most) {
        return new Reach(least, most);
    }

    /**
     * What {@code Σ coefs·position + constant} runs between.
     *
     * @param positions what each named position runs between; a position it has nothing for runs
     *                  the whole way, which leaves the sum unbounded in whichever directions that
     *                  position could push it
     */
    public static <A> Reach of(Map<A, ExactRatio> coefs, ExactRatio constant,
                               Function<A, Reach> positions) {
        ExactRatio least = constant;
        ExactRatio most = constant;
        boolean leastReached = true;
        boolean mostReached = true;
        for (Map.Entry<A, ExactRatio> each : coefs.entrySet()) {
            ExactRatio weight = each.getValue();
            Reach runs = positions.apply(each.getKey());
            if (runs == null) {
                runs = ANYWHERE;
            }
            ExactCut low = weight.signum() > 0 ? runs.least() : runs.most();
            ExactCut high = weight.signum() > 0 ? runs.most() : runs.least();
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
        return new Reach(least == null ? null : new ExactCut(least, leastReached),
                most == null ? null : new ExactCut(most, mostReached));
    }

    /** Whether either end was found. */
    public boolean saysNothing() {
        return least == null && most == null;
    }

    /**
     * Whether there is no value between the ends, so the form comes to nothing at all.
     *
     * <p>What this record means is the values a form is proven to run between, and a least above a
     * most names none of them. Said here because it is this type's own meaning rather than any one
     * reader's question — a reader working the answer out beside itself would be restating what
     * these two fields already say, and the two would agree only for as long as somebody kept them
     * so.
     *
     * <p>Not called bottom. That word belongs to a whole state over every position; this is one
     * form, and where a form is empty the state is empty too — but the reader that concludes the
     * second from the first is the one holding the state.
     *
     * <p>An end nobody found leaves the form running that way without stopping, which is the
     * opposite of empty, so both ends have to be there before this can be true. Which is the
     * distance between this and {@link #saysNothing}: that one is about what was found out, this one
     * about what was found out leaving room for a value.
     */
    public boolean isEmpty() {
        if (least == null || most == null) {
            return false;
        }
        int order = least.at().compareTo(most.at());
        // At one value the form is empty unless that value is reached from both sides: a form above
        // five and at most five runs nowhere, while one at least five and at most five runs at five.
        return order > 0 || (order == 0 && !(least.inclusive() && most.inclusive()));
    }
}
