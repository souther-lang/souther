package souther.compiler.check;

import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

/**
 * Whether every size a container of one type could have is the size of some value of it.
 *
 * <p>Decided by the type and not by the operation, which is why it is not
 * {@code EveryAnswerItCanGiveHasASourceValue}: a {@code List<Int>} of any length is written by
 * repeating an element, and a {@code List<Never>} of one has none. The type is read only as far as
 * it proves a value, and a type it does not read is not shown to have any, so a name the module
 * declares, which may carry rules or none to satisfy, leaves the sizes of the containers over it to
 * a row.
 *
 * <p>A set of three needs three elements that differ and a map of three three keys that differ, so
 * for those it is the element that has to be one the language never runs out of. A {@code Set<Bool>}
 * is capped at two and is none of these.
 */
public final class EverySizeAContainerHas {

    private static final ValueName LIST_LENGTH = ValueName.Stdlib.operation("List", "length");
    private static final ValueName SET_SIZE = ValueName.Stdlib.operation("Set", "size");
    private static final ValueName MAP_SIZE = ValueName.Stdlib.operation("Map", "size");

    private EverySizeAContainerHas() {
    }

    /** Whether {@code operation}, taken of a value of {@code container} that nothing restricts,
     *  answers every size some such value has. */
    public static boolean isTakenBy(ValueName operation, Type container) {
        if (operation.equals(LIST_LENGTH)) {
            return container instanceof Type.ListOf list && hasAValue(list.element());
        }
        if (operation.equals(SET_SIZE)) {
            return container instanceof Type.SetOf set && hasAsManyAsOneLikes(set.element());
        }
        if (operation.equals(MAP_SIZE)) {
            return container instanceof Type.MapOf map
                    && hasAsManyAsOneLikes(map.key()) && hasAValue(map.value());
        }
        return false;
    }

    /** Whether a value of {@code type} is shown to exist. */
    private static boolean hasAValue(Type type) {
        return switch (type) {
            case Type.Prim _, Type.ListOf _, Type.SetOf _, Type.MapOf _, Type.OptionOf _ -> true;
            case Type.TupleOf tuple -> tuple.elements().stream().allMatch(
                    EverySizeAContainerHas::hasAValue);
            default -> false;
        };
    }

    /** Whether values of {@code type} that differ are shown to be had in any number. */
    private static boolean hasAsManyAsOneLikes(Type type) {
        return switch (type) {
            case Type.Prim prim -> switch (prim) {
                case INT, STRING, DECIMAL, RATIONAL -> true;
                case BOOL, DATE, TIME, DATETIME, INSTANT -> false;
            };
            case Type.ListOf list -> hasAValue(list.element());
            default -> false;
        };
    }
}
