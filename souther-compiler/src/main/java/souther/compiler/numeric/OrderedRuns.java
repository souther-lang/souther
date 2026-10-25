package souther.compiler.numeric;

import java.util.ArrayList;
import java.util.List;

/**
 * The values of one order lying in runs, which is what a choice between ranges leaves a position.
 *
 * <p>Runs and not the ends around them. A choice between {@code value < 0} and {@code value > 100}
 * is the two of them: every value between is one neither alternative admits, and a reader choosing
 * a value for the position out of the ends around both would choose one of those.
 *
 * <p>Lowest first, with a value of the order between each run and the next that neither holds —
 * runs that overlap or touch are one run. So two of these holding the same values are equal, and
 * one run is the case of a position the rules leave an interval. A set holding nothing is one run
 * holding nothing, which is how an interval says it.
 *
 * <p>How many runs there are is bounded by what was written. A meet of two of these is at most as
 * many runs as both together less one, and a join at most as many as both together, so a position
 * holds no more runs than the comparisons the rules make of it, and nothing here gives up.
 *
 * @param runs the runs, lowest first and apart from each other; one run where they leave no gap
 */
public record OrderedRuns(List<OrderedInterval> runs) {

    public OrderedRuns {
        runs = List.copyOf(runs);
        if (runs.isEmpty()) {
            throw new IllegalArgumentException("a set of runs holding nothing is one empty run");
        }
    }

    /** The values of one interval, which is one run. */
    public static OrderedRuns of(OrderedInterval run) {
        return new OrderedRuns(List.of(run));
    }

    /**
     * The values of {@code runs} together, in the shape above: lowest first, those that overlap or
     * touch as one, and one run holding nothing where none of them holds a value.
     */
    public static OrderedRuns of(List<OrderedInterval> runs) {
        List<OrderedInterval> held = new ArrayList<>();
        for (OrderedInterval each : runs) {
            if (!each.holdsNothing()) {
                held.add(each);
            }
        }
        if (held.isEmpty()) {
            return of(runs.getFirst());
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
        return new OrderedRuns(out);
    }

    /** Whether these are one run, which an interval says as well as this does. */
    public boolean isOneRun() {
        return runs.size() == 1;
    }

    /** The ends around every run, which is every value of the runs and those between them. */
    public OrderedInterval hull() {
        return isOneRun() ? runs.getFirst()
                : new OrderedInterval(runs.getFirst().low(), runs.getLast().high());
    }

    /**
     * The values both hold, which is each run of one met with each run of the other it overlaps —
     * walked from the lowest, so each run is passed once.
     */
    public OrderedRuns meet(OrderedRuns other) {
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
        if (met.hull().holdsNothing()) {
            return List.of();
        }
        return met.runs.stream()
                .map(run -> new NumericDomain.Bounds(run.low(), run.high())).toList();
    }

    /** The values either holds. */
    public OrderedRuns join(OrderedRuns other) {
        List<OrderedInterval> both = new ArrayList<>(runs);
        both.addAll(other.runs);
        return of(both);
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
