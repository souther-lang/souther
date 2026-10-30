package souther.compiler.check;

import souther.compiler.abort.GetsPast;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.Type;

/**
 * How many elements a container of one type is shown to be had holding, from nought up.
 *
 * <p>What a container holds is the operation's to say ({@link TakenAs.HowManyItHolds}), what the
 * container is is the type's ({@link TypeView}), and how many values its elements have is
 * {@link ValuesShown}'s: a list of any length is written by repeating an element, a set of three
 * needs three elements that differ, and a map of three three keys that differ with a value under
 * each. This only puts the three together, and names no operation and no type.
 *
 * <p>A lower bound on what exists and never an upper bound on what does not: nought is not that a
 * size is out of reach but that nothing shows it in reach, so the empty container is the one size
 * every type is given.
 */
public final class EverySizeAContainerHas {

    private EverySizeAContainerHas() {
    }

    /**
     * The greatest size such that every size from nought up to it is the size of some value of
     * {@code container}, or null where {@code how} is no count of what a container of that shape
     * holds.
     *
     * @param how       how the number is taken of the container
     * @param container the type of the container, which nothing restricts
     */
    public static Long greatestShown(TakenAs how, Type container, RuleReadingContext reading) {
        if (!(how instanceof TakenAs.HowManyItHolds)) {
            return null;
        }
        RuleReadingSource source = reading.source();
        return switch (TypeView.shapeOf(container, source.inners(), source.symbols(),
                source.kinds(), source.sums())) {
            case Shape.Sequence sequence -> switch (sequence.kind()) {
                case LIST -> ValuesShown.of(sequence.element(), reading) >= 1 ? mostHeld() : 0L;
                case SET -> ValuesShown.of(sequence.element(), reading);
            };
            case Shape.Mapping map -> ValuesShown.of(map.value(), reading) >= 1
                    ? ValuesShown.of(map.key(), reading) : 0L;
            default -> null;
        };
    }

    /** How many elements a collection holds at most, which the language states once. */
    public static long mostHeld() {
        return GetsPast.MOST_ELEMENTS.longValueExact();
    }
}
