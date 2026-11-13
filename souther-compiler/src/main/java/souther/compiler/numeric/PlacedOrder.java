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
 * terms — and a form is walked once for every question put to it, where the places were worked out
 * once for the set. A walk that names a position with no place is the order's own.
 *
 * @param <A> what a position is
 */
final class PlacedOrder<A> implements CanonicalOrder<A> {

    private final Map<A, Integer> places;
    private final CanonicalOrder<A> order;
    private final CanonicalOrder<A> byPlace;

    PlacedOrder(Map<A, Integer> places, CanonicalOrder<A> order) {
        this.places = places;
        this.order = order;
        this.byPlace = new CanonicalOrder<>() {
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
        Integer placeOfOne = places.get(one);
        Integer placeOfOther = places.get(other);
        return placeOfOne != null && placeOfOther != null
                ? Integer.compare(placeOfOne, placeOfOther)
                : order.compare(one, other);
    }

    /**
     * {@link CanonicalOrder#walking}, and the same promise: the walk comes back in the order this
     * order puts the positions in, and two positions it cannot tell apart are refused. Walked by
     * places where every position has one and by the order itself where one has none, and both
     * hand back what the order's own walk does.
     */
    @Override
    public <T> List<T> walking(Collection<T> these, Function<T, A> at) {
        boolean everyOneIsPlaced = these.stream().allMatch(each -> places.containsKey(at.apply(each)));
        return everyOneIsPlaced ? byPlace.walking(these, at) : order.walking(these, at);
    }

    @Override
    public List<Map.Entry<A, ExactRatio>> walkOf(CanonicalForm<A> form,
                                                 Supplier<List<Map.Entry<A, ExactRatio>>> walk) {
        return order.walkOf(form, walk);
    }
}
