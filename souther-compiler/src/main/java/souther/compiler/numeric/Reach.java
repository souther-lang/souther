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
        Ends<A> ends = endsOf(positions);
        return new Reach(endOf(coefs, constant, ends, false), endOf(coefs, constant, ends, true));
    }

    /**
     * The upper end of {@link #of}, for a reader that asks for no other: the sums of the lower end
     * are not taken, and nothing is summed past a position with no end that way.
     *
     * @param ends the end of each position its weight reads, which is all of it this end asks
     */
    public static <A> ExactCut mostOf(Map<A, ExactRatio> coefs, ExactRatio constant,
                                      Ends<A> ends) {
        return endOf(coefs, constant, ends, true);
    }

    /**
     * The end of a position a sum reads where the position is weighed by a weight of sign
     * {@code sign}, for the sum's upper end or its lower one, as {@link #endWeighedBy} reads it; null
     * where the position has no end that way.
     */
    @FunctionalInterface
    public interface Ends<A> {

        ExactCut weighedBy(A position, int sign, boolean upper);
    }

    private static <A> Ends<A> endsOf(Function<A, Reach> positions) {
        return (position, sign, upper) -> {
            Reach runs = positions.apply(position);
            return (runs == null ? ANYWHERE : runs).endWeighedBy(sign, upper);
        };
    }

    /** {@link #mostOf(Map, ExactRatio, Ends)} over terms held in the order they are added in. */
    static <A> ExactCut mostOfTerms(OrderedTerms<A> terms, ExactRatio constant, Ends<A> ends) {
        return endOf(terms, constant, ends, true);
    }

    private static <A> ExactCut endOf(Map<A, ExactRatio> coefs, ExactRatio constant,
                                      Ends<A> ends, boolean upper) {
        return endOf(coefs.entrySet(), constant, ends, upper);
    }

    private static <A> ExactCut endOf(Iterable<? extends Map.Entry<A, ExactRatio>> terms,
                                      ExactRatio constant, Ends<A> ends, boolean upper) {
        ExactRatio sum = constant;
        boolean reached = true;
        for (Map.Entry<A, ExactRatio> each : terms) {
            ExactRatio weight = each.getValue();
            ExactCut end = ends.weighedBy(each.getKey(), weight.signum(), upper);
            if (end == null) {
                return null;
            }
            // A model's own run ends can put a term far enough apart in scale from the sum so far
            // that the exact arithmetic cannot hold it. Unheld here is the same answer as a position
            // with nothing for this direction: the sum runs unbounded that way rather than at a value
            // nothing composed.
            ExactRatio before = sum;
            sum = weight.times(end.at()).flatMap(before::plus).orNull();
            if (sum == null) {
                return null;
            }
            reached &= end.inclusive();
        }
        return new ExactCut(sum, reached);
    }

    /**
     * The end of this position a sum it is weighed in by a weight of sign {@code sign} reads for its
     * own upper end, or its lower one: the same end where the weight pulls the sum up, the other
     * where it pulls it down. A weight of nought reads the lower end for the upper and the upper for
     * the lower, as a pull down does.
     */
    public ExactCut endWeighedBy(int sign, boolean upper) {
        return readsTheMost(sign, upper) ? most : least;
    }

    /** Whether the end {@link #endWeighedBy} reads for {@code sign} and {@code upper} is the
     *  greatest, and not the least. */
    public static boolean readsTheMost(int sign, boolean upper) {
        return (sign > 0) == upper;
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
