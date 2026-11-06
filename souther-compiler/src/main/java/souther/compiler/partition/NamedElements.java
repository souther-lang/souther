package souther.compiler.partition;

import souther.compiler.inputs.ElementsNamed;

import java.util.Objects;

/**
 * Which elements the names in a condition on the way stood for, and which condition it was.
 *
 * <p>What a condition states of an element is said at the element's position, and the position
 * says an element and not which one: {@code a.n < 0} and {@code b.n >= 1} over {@code x.items}
 * both state something of {@code x.items[*].n}. So the names are kept on the entry made of the
 * condition, where the way is put together, and what may be composed as one value is decided
 * there ({@link ElementsOnTheWay}).
 *
 * <p>The condition goes with them, because an entry its names keep apart from the rest of the way
 * is declined there, and a decline says which condition it is.
 *
 * @param condition which condition of the reading the entry was read off; null only where
 *                  {@code elements} is empty, since nothing is ever declined for those
 * @param elements  the elements its names stood for
 */
public record NamedElements(ConditionOccurrence condition, ElementsNamed elements) {

    /** Read through no name for an element. */
    public static final NamedElements NONE = new NamedElements(null, ElementsNamed.NONE);

    public NamedElements {
        Objects.requireNonNull(elements, "the elements a condition was read of, or none");
        if (condition == null && !elements.isEmpty()) {
            throw new IllegalArgumentException("elements named are named by some condition: "
                    + elements);
        }
    }

    /** {@code elements}, named by {@code condition}: {@link #NONE} where nothing was. */
    public static NamedElements of(ConditionOccurrence condition, ElementsNamed elements) {
        return elements.isEmpty() ? NONE : new NamedElements(condition, elements);
    }
}
