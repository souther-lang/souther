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
public record OrderedIntervals<A>(Map<A, OrderedInterval> ranges) {

    public OrderedIntervals {
        // Kept in the order the positions were read. What is written out of these has to come out
        // the same on two runs of the compiler, and the iteration order of an immutable copy does
        // not.
        ranges = Collections.unmodifiableMap(new LinkedHashMap<>(ranges));
    }

    /** Nothing read, so every position holds every value its order has. */
    public static <A> OrderedIntervals<A> top() {
        return new OrderedIntervals<>(Map.of());
    }

    /** One position said to lie inside {@code range}. */
    public static <A> OrderedIntervals<A> at(A position, OrderedInterval range) {
        return new OrderedIntervals<>(Map.of(position, range));
    }

    /** What {@code position} is left, every value of its order where nothing was said. */
    public OrderedInterval at(A position) {
        return ranges.getOrDefault(position, OrderedInterval.OPEN);
    }

    /** Whether some position is left no value, so that nothing satisfies these rules. */
    public boolean isBottom() {
        return ranges.values().stream().anyMatch(OrderedInterval::holdsNothing);
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
        return new OrderedIntervals<>(out);
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
     * <p>Both sides holding nothing is a different case and is not that one. No side speaks for the
     * other there, and answering with either would settle which position is named by the order the
     * two were written in — so they are met, which is empty whichever way round it is read and keeps
     * every position either of them left empty.
     */
    public OrderedIntervals<A> join(OrderedIntervals<A> other) {
        if (isBottom() && other.isBottom()) {
            return meet(other);
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
        return new OrderedIntervals<>(out);
    }
}
