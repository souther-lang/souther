package souther.compiler.observe;

import souther.compiler.numeric.Place;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.function.Function;

/**
 * The order the parts of a collection that states none are written in: the elements of a set and the
 * entries of a map.
 *
 * <p>Where every part sits on an order of its type, they are written in that order, and the text is
 * the tie between two parts at one place. Where any part has no place, all of them are written in
 * the order of their text, so that one rule orders the whole collection and never a different one
 * for each pair.
 *
 * <p>What the order is belongs to the type and is handed in as {@code placeOf}; this knows no type.
 * Every writer of such a collection asks here, so what a fixture offers and what a report shows
 * cannot come to order the same collection two ways.
 */
public final class UnorderedOrder {

    private UnorderedOrder() {
    }

    private record Keyed<T>(T part, Place place, String text) {
    }

    /**
     * {@code parts} in the order a collection that states none is written in. The list handed in is
     * left as it is.
     *
     * @param placeOf where a part sits on the order of its type, or null where it has none. For an
     *                entry, where its key does
     * @param textOf  how a part is written, asked once of each
     */
    public static <T> List<T> of(List<T> parts, Function<T, Place> placeOf,
                                 Function<T, String> textOf) {
        List<Keyed<T>> keyed = new ArrayList<>(parts.size());
        boolean byValue = true;
        for (T each : parts) {
            Place place = placeOf.apply(each);
            byValue &= place != null;
            keyed.add(new Keyed<>(each, place, textOf.apply(each)));
        }
        Comparator<Keyed<T>> byText = Comparator.comparing(Keyed::text);
        keyed.sort(byValue ? Comparator.<Keyed<T>, Place>comparing(Keyed::place).thenComparing(byText)
                : byText);
        return keyed.stream().map(Keyed::part).toList();
    }
}
