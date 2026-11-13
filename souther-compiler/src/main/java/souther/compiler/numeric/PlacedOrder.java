package souther.compiler.numeric;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.function.ToIntFunction;

/**
 * An order, walking the positions it holds a place for by those places.
 *
 * <p>The places are what {@link ClosureQuestion#placesIn} says for a set of positions under the
 * order, so a walk of positions all in the set comes out as the order walks it, and without a
 * comparison of two positions in it. A comparison can be dear — it reads the structure of two
 * terms — and a form is walked once for every question put to it, where the places are worked out
 * once for the set. A walk that names a position with no place is the order's own.
 *
 * <p>The places are asked for when a walk first has two positions to put in order, and never
 * before: an order that is handed to a reading and walks nothing with two positions in it costs
 * nothing. Asked for once, and held here, so what outlives this order is whatever the supplier
 * keeps and nothing it did not.
 *
 * @param <A> what a position is
 */
final class PlacedOrder<A> implements CanonicalOrder<A> {

    /** The places, and the order that puts positions in them. */
    private record Tabled<A>(Map<A, Integer> places, CanonicalOrder<A> byPlace) {}

    private final Supplier<Map<A, Integer>> making;
    private final CanonicalOrder<A> order;

    /** Worked out on the first walk that needs it. Two threads that meet at that walk work out the
     *  same places and either is the one held, and a record is read whole whichever it is. */
    private Tabled<A> tabled;

    PlacedOrder(Supplier<Map<A, Integer>> making, CanonicalOrder<A> order) {
        this.making = making;
        this.order = order;
    }

    private Tabled<A> table() {
        Tabled<A> had = tabled;
        if (had == null) {
            Map<A, Integer> places = making.get();
            had = new Tabled<>(places, byPlace(places));
            tabled = had;
        }
        return had;
    }

    private static <A> CanonicalOrder<A> byPlace(Map<A, Integer> places) {
        return new CanonicalOrder<>() {
            @Override
            public int compare(A one, A other) {
                return Integer.compare(places.get(one), places.get(other));
            }

            @Override
            public ToIntFunction<A> placeOf() {
                return places::get;
            }
        };
    }

    @Override
    public int compare(A one, A other) {
        Tabled<A> had = tabled;
        if (had != null) {
            Integer placeOfOne = had.places().get(one);
            Integer placeOfOther = had.places().get(other);
            if (placeOfOne != null && placeOfOther != null) {
                return Integer.compare(placeOfOne, placeOfOther);
            }
        }
        return order.compare(one, other);
    }

    /**
     * {@link CanonicalOrder#walking}, and the same promise: the walk comes back in the order this
     * order puts the positions in, and two positions it cannot tell apart are refused. Walked by
     * places where every position has one and by the order itself where one has none, and both
     * hand back what the order's own walk does.
     */
    @Override
    public <T> List<T> walking(Collection<T> these, Function<T, A> at) {
        if (these.size() < 2) {
            return order.walking(these, at);
        }
        Tabled<A> held = table();
        boolean everyOneIsPlaced =
                these.stream().allMatch(each -> held.places().containsKey(at.apply(each)));
        return everyOneIsPlaced ? held.byPlace().walking(these, at) : order.walking(these, at);
    }

    @Override
    public List<Map.Entry<A, ExactRatio>> walkOf(CanonicalForm<A> form,
                                                 Supplier<List<Map.Entry<A, ExactRatio>>> walk) {
        return order.walkOf(form, walk);
    }
}
