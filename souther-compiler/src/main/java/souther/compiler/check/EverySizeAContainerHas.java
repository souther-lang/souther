package souther.compiler.check;

import souther.compiler.abort.GetsPast;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.Type;

/**
 * How many elements a container of one type is shown to be had holding, from nought up.
 *
 * <p>What a container holds is the operation's to say ({@link TakenAs.HowManyItHolds}), and how
 * many of them a type can be given is this type's: a {@code List<Int>} of any length is written by
 * repeating an element, a {@code List<Never>} of one has none, and a {@code Set<Bool>} is capped at
 * two by how many booleans there are. So the question is asked of the way the number is taken and
 * of the shape of what is taken it of, and not of an operation by its name.
 *
 * <p>A lower bound on what exists and never an upper bound on what does not. A type this reads no
 * values of is shown to have none, which leaves its containers the empty one, and says nothing of
 * whether it has any: a name the module declares may carry rules, or none to satisfy, and a count
 * of values this does not work out is not a count of none ({@link Cardinality}).
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
    public static Long greatestShown(TakenAs how, Type container) {
        if (!(how instanceof TakenAs.HowManyItHolds)) {
            return null;
        }
        return switch (container) {
            case Type.ListOf list -> distinctShown(list.element()) >= 1 ? mostHeld() : 0L;
            case Type.SetOf set -> distinctShown(set.element());
            case Type.MapOf map -> distinctShown(map.value()) >= 1 ? distinctShown(map.key()) : 0L;
            default -> null;
        };
    }

    /**
     * At least this many values of {@code type} that differ are shown to exist, ending at the most
     * a container holds: a count past it is no more to the question asked. Nought where none is
     * shown.
     */
    private static long distinctShown(Type type) {
        return switch (type) {
            case Type.Prim prim -> switch (prim) {
                case INT, STRING, DECIMAL, RATIONAL -> mostHeld();
                case BOOL, DATE, TIME, DATETIME, INSTANT -> 2L;
            };
            case Type.ListOf list -> distinctShown(list.element()) >= 1 ? mostHeld() : 1L;
            case Type.SetOf set -> powerOfTwo(distinctShown(set.element()));
            case Type.MapOf map -> distinctShown(map.key()) >= 1 && distinctShown(map.value()) >= 1
                    ? 2L : 1L;
            case Type.OptionOf option -> Math.min(mostHeld(), 1 + distinctShown(option.element()));
            case Type.TupleOf tuple -> {
                long product = 1;
                for (Type each : tuple.elements()) {
                    long shown = distinctShown(each);
                    if (shown == 0) {
                        yield 0L;
                    }
                    product = shown > mostHeld() / product ? mostHeld() : product * shown;
                }
                yield product;
            }
            default -> 0L;
        };
    }

    /** Two to the {@code power}, ending at the most a container holds. */
    private static long powerOfTwo(long power) {
        return power >= Long.numberOfLeadingZeros(mostHeld()) - 1 ? mostHeld()
                : Math.min(mostHeld(), 1L << power);
    }

    /** How many elements a collection holds at most, which the language states once. */
    public static long mostHeld() {
        return GetsPast.MOST_ELEMENTS.longValueExact();
    }
}
