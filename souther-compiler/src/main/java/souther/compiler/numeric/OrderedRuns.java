package souther.compiler.numeric;

import java.util.ArrayList;
import java.util.List;

/**
 * The values of one order the rules leave a position, as the runs they lie in.
 *
 * <p>Runs and not the ends around them. A choice between {@code value < 0} and {@code value > 100}
 * is the two of them: every value between is one neither alternative admits, and a reader choosing
 * a value for the position out of the ends around both would choose one of those.
 *
 * <p><b>Every shape the rules can leave, and each said as itself.</b> Met with another rule, two
 * runs may come to one run or to none, and both are answers: one run is where the position stops
 * and none is a position nothing can stand at. So this is the whole of what the order leaves and
 * never a note beside an interval kept somewhere else — a reader holding one of these holds the
 * answer, and the ends around it ({@link #hull}) are a projection of it for a reader of ends.
 *
 * <p>Lowest first, with a value of the order between each run and the next that neither holds —
 * runs that overlap or touch are one run. Made only by the factories here, which put what they are
 * handed into that shape, so the walks below can take it for granted and two of these holding the
 * same values are equal.
 *
 * <p>How many runs there are is bounded by what was written. A meet of two of these is at most as
 * many runs as both together less one, and a join at most as many as both together, so a position
 * holds no more runs than the comparisons the rules make of it, and nothing here gives up.
 */
public final class OrderedRuns {

    /** The runs, lowest first and apart from each other; none where nothing is left. */
    private final List<OrderedInterval> runs;

    /**
     * An interval holding nothing, as the reading came to it, where nothing is left and an interval
     * said so; null otherwise.
     *
     * <p>Kept for {@link #hull}: a reader of ends asks for an interval, and one holding nothing is
     * how an interval says nothing is left. Which ends it has is no part of what this holds, so it
     * takes no part in equality.
     */
    private final OrderedInterval nothing;

    private OrderedRuns(List<OrderedInterval> runs, OrderedInterval nothing) {
        this.runs = List.copyOf(runs);
        this.nothing = nothing;
    }

    /**
     * No value of the order at all, as a reading says it that reached no interval to say it with —
     * the numbers of a position admitting no assignment, say. There are no ends around nothing, so
     * {@link #hull} has none to give.
     */
    public static OrderedRuns nothing() {
        return new OrderedRuns(List.of(), null);
    }

    /** What {@code rel} against {@code at} leaves a value on the order: one run, or the two either
     *  side of the place a disequality leaves out. */
    public static OrderedRuns leftBy(Rel rel, Place at) {
        return rel == Rel.NE
                ? of(List.of(OrderedInterval.leftBy(Rel.LT, at),
                        OrderedInterval.leftBy(Rel.GT, at)))
                : of(OrderedInterval.leftBy(rel, at));
    }

    /** The values of one interval, which is one run, or none where it holds nothing. */
    public static OrderedRuns of(OrderedInterval run) {
        return run.holdsNothing() ? new OrderedRuns(List.of(), run)
                : new OrderedRuns(List.of(run), null);
    }

    /**
     * The values of {@code runs} together, in the shape above: lowest first, those that overlap or
     * touch as one, and none where none of them holds a value.
     *
     * @param runs at least one interval, so that nothing left is said by one of them
     */
    public static OrderedRuns of(List<OrderedInterval> runs) {
        List<OrderedInterval> held = new ArrayList<>();
        for (OrderedInterval each : runs) {
            if (!each.holdsNothing()) {
                held.add(each);
            }
        }
        if (held.isEmpty()) {
            return new OrderedRuns(List.of(), runs.getFirst());
        }
        held.sort(OrderedRuns::byLowerEnd);
        List<OrderedInterval> out = new ArrayList<>();
        OrderedInterval reaching = held.getFirst();
        for (OrderedInterval next : held.subList(1, held.size())) {
            if (apart(reaching, next)) {
                out.add(reaching);
                reaching = next;
            } else {
                reaching = reaching.join(next);
            }
        }
        out.add(reaching);
        return new OrderedRuns(out, null);
    }

    /** The runs, lowest first; none where nothing is left. */
    public List<OrderedInterval> runs() {
        return runs;
    }

    /** Whether the rules leave the position no value of its order. */
    public boolean holdsNothing() {
        return runs.isEmpty();
    }

    /** Whether the values are one run, which an interval says as well as this does. */
    public boolean isOneRun() {
        return runs.size() == 1;
    }

    /** Whether {@code at} is a value of one of the runs. */
    public boolean admits(Place at) {
        return runs.stream().anyMatch(run -> run.admits(at));
    }

    /**
     * The ends around every run, which is every value of the runs and those between them — an
     * interval holding nothing where nothing is left and an interval said so.
     *
     * @throws IllegalStateException where nothing is left and no interval said it
     *                               ({@link #nothing()}): a reader of ends asking that is asking
     *                               where a position stops of one that has no values
     */
    public OrderedInterval hull() {
        if (holdsNothing()) {
            if (nothing == null) {
                throw new IllegalStateException("no ends around a position no value stands at");
            }
            return nothing;
        }
        return isOneRun() ? runs.getFirst()
                : new OrderedInterval(runs.getFirst().low(), runs.getLast().high());
    }

    /**
     * The values both hold, which is each run of one met with each run of the other it overlaps —
     * walked from the lowest, so each run is passed once.
     */
    public OrderedRuns meet(OrderedRuns other) {
        if (holdsNothing()) {
            return this;
        }
        if (other.holdsNothing()) {
            return other;
        }
        List<OrderedInterval> out = new ArrayList<>();
        int i = 0;
        int j = 0;
        while (i < runs.size() && j < other.runs.size()) {
            OrderedInterval here = runs.get(i);
            OrderedInterval there = other.runs.get(j);
            out.add(here.meet(there));
            // Whichever stops first has met every run of the other it reaches.
            if (Endpoint.upper(here.high(), there.high()) == here.high()) {
                i++;
            } else {
                j++;
            }
        }
        return of(out);
    }

    /** The values either holds. */
    public OrderedRuns join(OrderedRuns other) {
        if (holdsNothing()) {
            return other;
        }
        if (other.holdsNothing()) {
            return this;
        }
        List<OrderedInterval> both = new ArrayList<>(runs);
        both.addAll(other.runs);
        return of(both);
    }

    /**
     * The part of {@code bounds} inside each run, lowest first, and none where it holds nothing of
     * any of them — which is a range a reader would otherwise have looked for a value in, and the
     * values it holds are the gaps every alternative refuses.
     *
     * @param bounds where a reader has the value stopping, or null where nothing stops it
     */
    public List<NumericDomain.Bounds> partsOf(NumericDomain.Bounds bounds) {
        OrderedRuns met = bounds == null ? this
                : meet(of(new OrderedInterval(bounds.min(), bounds.max())));
        return met.runs.stream()
                .map(run -> new NumericDomain.Bounds(run.low(), run.high())).toList();
    }

    /**
     * Whether this and {@code other} hold the same values, asked of each run's values rather than
     * of how its ends were written ({@link OrderedInterval#sameValuesAs}).
     */
    public boolean sameValuesAs(OrderedRuns other) {
        if (runs.size() != other.runs.size()) {
            return false;
        }
        for (int each = 0; each < runs.size(); each++) {
            if (!runs.get(each).sameValuesAs(other.runs.get(each))) {
                return false;
            }
        }
        return true;
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof OrderedRuns it && runs.equals(it.runs);
    }

    @Override
    public int hashCode() {
        return runs.hashCode();
    }

    @Override
    public String toString() {
        return holdsNothing() ? "OrderedRuns[nothing]" : "OrderedRuns" + runs;
    }

    /**
     * Whether a value of the order lies above {@code lower} and below {@code upper}, which starts
     * no lower than it does — so that neither holds the value and the two are runs apart.
     *
     * <p>Asked as a range of its own: the values past the end of one and short of the start of the
     * other. A run ending at a place it holds and one starting just past it leave no value between
     * them on a dense order, and leave none on a counted one only where the two places are
     * neighbours — which is the order's to say, so they are kept apart here and hold the same
     * values either way.
     */
    private static boolean apart(OrderedInterval lower, OrderedInterval upper) {
        if (lower.high() == null || upper.low() == null) {
            return false;
        }
        return Endpoint.someValueLiesBetween(flipped(lower.high()), flipped(upper.low()));
    }

    /** The same place, held where it was left out and left out where it was held. */
    private static Endpoint flipped(Endpoint end) {
        return new Endpoint(end.at(), !end.inclusive());
    }

    /** Lowest first, an open lower end lowest of all, and at one place an end holding it first. */
    private static int byLowerEnd(OrderedInterval one, OrderedInterval other) {
        Endpoint a = one.low();
        Endpoint b = other.low();
        if (a == null || b == null) {
            return a == null ? (b == null ? 0 : -1) : 1;
        }
        int order = a.at().compareTo(b.at());
        if (order != 0) {
            return order;
        }
        return Boolean.compare(b.inclusive(), a.inclusive());
    }
}
