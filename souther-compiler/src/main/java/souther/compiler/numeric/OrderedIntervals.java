package souther.compiler.numeric;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * What the ordered rules leave each position, over all the rules a reading took in.
 *
 * <p>A state and not an interval. A rule is written about a whole value and may name several of its
 * positions, and the connectives join whole readings rather than the range at one position — so what
 * a conjunction and a disjunction are applied to is this, and the arithmetic at one position is
 * {@link OrderedInterval}.
 *
 * <p><b>Bottom is a state and not always a position.</b> The rules leave nothing where some position
 * is left no value — and also where every alternative of a choice is one nobody can take, which is
 * not a fact about any one position. The second is {@code nothing}, and it is why the two cannot be
 * one answer: a choice between {@code a < ""} and {@code b < ""} admits nothing, and neither
 * {@code a} nor {@code b} is a position the choice leaves empty, since each alternative admits every
 * value of the other's.
 *
 * <p><b>A position not held here is every value its order has.</b> Which is what makes a meet with
 * what the rules said the whole answer, and what makes a join drop a position only one side bounded:
 * joining with everything is everything.
 *
 * <p><b>One direction only.</b> This exists to decide that a position holds no value, so every
 * operation that cannot be exact widens. A choice between two ranges is the ends around both, which
 * admits values neither alternative does; a state that narrowed there would refuse a model somebody
 * can write.
 *
 * <p>Apart from {@link NumericDomain}, which relates positions to each other by differences and can
 * only do so over numbers a model adds. This relates no two positions and holds every order there
 * is — so a rule comparing a date against a written one lands here, and one comparing two fields of
 * a record lands there. Both may hold the same rule about an {@code Int}, and neither is the other's
 * copy: what each of them can show is its own, and a contradiction shown anywhere is a contradiction.
 */
public record OrderedIntervals<A>(Map<A, OrderedInterval> ranges, boolean nothing) {

    public OrderedIntervals {
        // Kept in the order the positions were read. What is written out of these has to come out
        // the same on two runs of the compiler, and the iteration order of an immutable copy does
        // not.
        ranges = Collections.unmodifiableMap(new LinkedHashMap<>(ranges));
    }

    /** Nothing read, so every position holds every value its order has. */
    public static <A> OrderedIntervals<A> top() {
        return new OrderedIntervals<>(Map.of(), false);
    }

    /** One position said to lie inside {@code range}. */
    public static <A> OrderedIntervals<A> at(A position, OrderedInterval range) {
        return new OrderedIntervals<>(Map.of(position, range), false);
    }

    /**
     * This where it already holds nothing, and a state holding nothing where it does not.
     *
     * <p>What a caller says when something outside this showed that nothing satisfies the rules —
     * another domain reading the same clause, say. Nothing is claimed about any position: what is
     * known is about the whole, and writing it at a position would name one the rules are fine with.
     */
    public OrderedIntervals<A> leavingNothing() {
        return isBottom() ? this : new OrderedIntervals<>(Map.of(), true);
    }

    /** What {@code position} is left, every value of its order where nothing was said. */
    public OrderedInterval at(A position) {
        return ranges.getOrDefault(position, OrderedInterval.OPEN);
    }

    /** Whether nothing satisfies these rules, at a position or otherwise. */
    public boolean isBottom() {
        return nothing || ranges.values().stream().anyMatch(OrderedInterval::holdsNothing);
    }

    /**
     * Every position the rules leave no value at.
     *
     * <p>All of them and not one. Which of several a refusal is written about is settled by the
     * order the positions are declared in, which is a fact about the declaration and not about this
     * — a state answering with one of them would settle it by the order the clauses happened to be
     * read in.
     */
    public Set<A> holdingNothing() {
        Set<A> out = new LinkedHashSet<>();
        ranges.forEach((position, range) -> {
            if (range.holdsNothing()) {
                out.add(position);
            }
        });
        return Collections.unmodifiableSet(out);
    }

    /** Both readings holding at once. */
    public OrderedIntervals<A> meet(OrderedIntervals<A> other) {
        Map<A, OrderedInterval> out = new LinkedHashMap<>(ranges);
        other.ranges.forEach((position, range) -> out.merge(position, range, OrderedInterval::meet));
        return new OrderedIntervals<>(out, nothing || other.nothing);
    }

    /**
     * Either reading holding.
     *
     * <p>Over the positions both spoke about, since a position one of them left open is one the two
     * of them together leave open.
     *
     * <p>A side holding nothing is an alternative nobody can take, so the choice is the other one.
     * Asked of the whole side rather than position by position: a branch with one position empty is
     * a branch no value satisfies, and hulling its other positions in would widen the answer by ends
     * no value of the model is ever at.
     *
     * <p><b>Both sides holding nothing is a different case.</b> No side speaks for the other there,
     * so answering with either would settle which position is named by the order the two were
     * written in. Nor may the two be met: a meet is a conjunction, and the alternatives were never
     * stated together — {@code (a < "" && b == 0) || (a < "" && b == 1)} met is a {@code b} bounded
     * at 0 and at 1, which is a contradiction neither alternative contains and a position the rules
     * are fine with.
     *
     * <p>What the choice leaves empty is what <em>every</em> alternative leaves empty, which is the
     * positions in both. Where there are none, the choice still admits nothing and no position is at
     * fault, and that is said as itself.
     */
    public OrderedIntervals<A> join(OrderedIntervals<A> other) {
        if (isBottom() && other.isBottom()) {
            Map<A, OrderedInterval> both = new LinkedHashMap<>();
            for (A position : holdingNothing()) {
                if (other.holdingNothing().contains(position)) {
                    both.put(position, at(position).meet(other.at(position)));
                }
            }
            return new OrderedIntervals<>(both, true);
        }
        if (isBottom()) {
            return other;
        }
        if (other.isBottom()) {
            return this;
        }
        Map<A, OrderedInterval> out = new LinkedHashMap<>();
        ranges.forEach((position, range) -> {
            OrderedInterval there = other.ranges.get(position);
            if (there != null) {
                out.put(position, range.join(there));
            }
        });
        return new OrderedIntervals<>(out, false);
    }
}
