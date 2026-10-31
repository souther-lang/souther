package souther.compiler.observe;

import souther.compiler.numeric.Place;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.function.Function;

/**
 * The order a set's elements are written in, for a set states none.
 *
 * <p>Where every element sits on an order of its type, they are written in that order, and the text
 * is the tie between two elements at one place. Where any element has no place, all of them are
 * written in the order of their text, so that one rule orders the whole set and never a different
 * one for each pair.
 *
 * <p>What the order is belongs to the type and is handed in as {@code placeOf}; this knows no type.
 */
public final class CanonicalSetOrder {

    private CanonicalSetOrder() {
    }

    private record Keyed<T>(T element, Place place, String text) {
    }

    /**
     * {@code elements} in the order a set is written in. The list handed in is left as it is.
     *
     * @param placeOf where an element sits on the order of its type, or null where it has none
     * @param textOf  how an element is written
     */
    public static <T> List<T> of(List<T> elements, Function<T, Place> placeOf,
                                 Function<T, String> textOf) {
        List<Keyed<T>> keyed = new ArrayList<>(elements.size());
        boolean byValue = true;
        for (T each : elements) {
            Place place = placeOf.apply(each);
            byValue &= place != null;
            keyed.add(new Keyed<>(each, place, textOf.apply(each)));
        }
        Comparator<Keyed<T>> byText = Comparator.comparing(Keyed::text);
        keyed.sort(byValue ? Comparator.<Keyed<T>, Place>comparing(Keyed::place).thenComparing(byText)
                : byText);
        return keyed.stream().map(Keyed::element).toList();
    }
}
