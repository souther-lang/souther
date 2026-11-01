package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.check.NumericMeasures;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.CountDomain;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.numeric.Place;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;

/**
 * The most elements of a container a count of them meeting a statement comes to, where something
 * says there is a most.
 *
 * <p>Two things say it. The count is of elements the container holds, so it is never more than the
 * most the container holds — what the rules and the type leave the number that is its size, the
 * number a rule taking {@code Set.size} of it is read against. And a set holds each value of its
 * element once, so where its element has only so many values the count is never more than how
 * many of those meet the statement; a set of records of two truths, counted for one of them, holds
 * at most the two records where that one is true.
 *
 * <p>The second is read off the element's values one at a time, each read as the element alone
 * ({@link ElementValues#alone}): a statement reading anything but the element — another position,
 * the container, its other elements — is told it could not walk there, and a value is counted
 * unless the statement fails of it. What the statement fails of with nothing else known, it fails
 * of whatever else stands beside the value. And it is read only where every value the element can
 * take is listed: each part with only so many values at all of them, and a number at every value
 * the rules leave it, where those are few enough to list. A value too many — one the rules refuse
 * elsewhere — makes the end looser and never wrong.
 *
 * <p>Where the figure the listing is held to stops it, the count keeps the most its container
 * holds, and the composer looking for a row between the two lists the same values, stops at the
 * same figure, and says so.
 */
final class HowManyCanMeet {

    private HowManyCanMeet() {
    }

    /**
     * The most {@code counted} comes to as {@code read} has its container, or none where nothing
     * says.
     *
     * <p>Worked out once for each count a reading reads. The answer is a function of which count
     * it is and of the reading, and a count is cut at every comparison written about it, each of
     * which would otherwise list the element's values and read each of them again.
     */
    static Optional<Count> of(CountedElements counted, InputReading read) {
        Known known = read.derived(Known.class, _ -> new Known());
        Optional<Count> kept = known.ends.get(counted.identity());
        if (kept == null) {
            kept = workedOut(counted, read);
            known.ends.put(counted.identity(), kept);
        }
        return kept;
    }

    /** The ends worked out for the counts one reading reads, by which count each is. */
    private static final class Known {
        private final Map<CountedElements.Identity, Optional<Count>> ends =
                new ConcurrentHashMap<>();
    }

    private static Optional<Count> workedOut(CountedElements counted, InputReading read) {
        TermPath container = counted.container();
        Position at = read.domain().at(container);
        if (at == null) {
            return Optional.empty();
        }
        long held = mostHeld(container, at.type(), read);
        long most = Math.min(held, ofTheValuesMeeting(counted, at.type(), read, held));
        return most == Long.MAX_VALUE ? Optional.empty() : Optional.of(Count.of(most));
    }

    /**
     * The most the container at {@code container} holds, or {@link Long#MAX_VALUE} where nothing
     * says: what the rules leave the number that is how many it holds, which carries what its type
     * leaves it as well.
     *
     * <p>Not {@link Quantities#mostHeldAt}, which answers only where a rule counts the container —
     * the question there is whether the rules leave it room, and a container no rule measures is
     * not taken to be one they leave none.
     */
    private static long mostHeld(TermPath container, Type type, InputReading read) {
        NumericTerm.TakenOf held = sizeOf(container, type, read);
        NumericDomain.Bounds runs = held == null ? null : read.quantities().runsBetween(held);
        int most = runs == null ? Integer.MAX_VALUE : CountDomain.mostFrom(runs.max());
        // Below none is a size no container has, which is the rules leaving the input nothing and
        // is said where that is asked; it is no end for a count.
        return most == Integer.MAX_VALUE || most < 0 ? Long.MAX_VALUE : most;
    }

    /** The number that is how many the container at {@code container} holds, or null where its
     *  type has no such number. */
    private static NumericTerm.TakenOf sizeOf(TermPath container, Type type, InputReading read) {
        RuleReadingSource source = read.rules();
        ValueName.Stdlib size = NumericMeasures.takenOf(type, source.inners());
        return size == null ? null : NumericTerm.TakenOf.howManyHeldAt(size, container, type,
                source.inners(), source.symbols());
    }

    /**
     * Whether {@code term} is how many the container {@code counted} counts the elements of
     * holds: the number a count of some of its elements is never more than.
     */
    static boolean isTheSizeOfTheContainer(CountedElements counted, NumericTerm term,
                                           InputReading read) {
        Position at = read.domain().at(counted.container());
        return at != null && term.equals(sizeOf(counted.container(), at.type(), read));
    }

    /**
     * How many values of the element of a set the statement does not fail of, or
     * {@link Long#MAX_VALUE} where that is no bound on the count.
     *
     * <p>Of a set, which holds each value of its element once. A list holds one over again, and a
     * map holds each key once with values that may repeat, so how many of its keys there are is
     * the end of its entries, and that end is the most it holds.
     *
     * <p>The reading stops once as many as {@code held} meet it, past which the count is bounded by
     * the container and not by these.
     */
    private static long ofTheValuesMeeting(CountedElements counted, Type type, InputReading read,
                                           long held) {
        RuleReadingSource source = read.rules();
        if (!(TypeView.shapeOf(type, source.inners(), source.symbols(), source.kinds(),
                        source.sums()) instanceof Shape.Sequence(Shape.Sequence.Kind kind,
                                Type element))
                || kind != Shape.Sequence.Kind.SET) {
            return Long.MAX_VALUE;
        }
        Quantities quantities = read.quantities();
        ElementValues values = ElementValues.of(counted.container(), element, read.ruleReading(),
                (at, _) -> everyValueAt(at, quantities));
        if (values == null || !values.listed().all()) {
            return Long.MAX_VALUE;
        }
        long meet = 0;
        for (ObservedValue value : values.listed().values()) {
            if (meet >= held) {
                return held;
            }
            if (!(counted.perElement().at(values.alone(value))
                    instanceof AStatementAtARow.Answer.Fails)) {
                meet++;
            }
        }
        return meet;
    }

    /**
     * Every value in the run the rules leave the number at {@code at}, or null where that is not a
     * few values this can list: a number on no order, one whose run has no end or fills, or one
     * with more values in it than the element is listed at. A value the rules take out of the run
     * is listed too, which makes the end looser and never wrong.
     */
    private static List<ObservedValue> everyValueAt(TermPath at, Quantities quantities) {
        NumericTerm term = new NumericTerm.ValueOf(at);
        TermOrders orders = quantities.ordersOf(term);
        Carrier carrier = orders == null ? null : orders.observed();
        NumericDomain.Bounds run = carrier == null ? null : quantities.runsBetween(term);
        List<Place> every = run == null ? null : carrier.firstPlacesIn(
                new OrderedInterval(run.min(), run.max()), ElementValues.mostOfAPart());
        if (every == null) {
            return null;
        }
        List<ObservedValue> out = new ArrayList<>();
        for (Place each : every) {
            out.add(carrier.valueOf(each));
        }
        return out;
    }
}
