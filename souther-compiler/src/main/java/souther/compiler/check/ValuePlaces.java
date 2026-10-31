package souther.compiler.check;

import souther.compiler.numeric.Place;
import souther.compiler.observe.Asserted;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.Set;

/**
 * Where a value standing at one position sits on the order of its number, for whatever writes a
 * collection that states no order.
 *
 * <p>The one answer to that question. A fixture offered for a row and a report of two values that
 * differ both put the parts of a set or a map in the order of their values, and each asks here with
 * the type of the position: the names the position wears are the type's ({@link TypeView}), the
 * order is the carrier's ({@link Carrier}), and a value is read for its place after the names are
 * off it, whether it was observed or stated. A reader that took the names off by its own walk, or
 * read a place off a value's text, would be a second answer to where a number is.
 *
 * <p>Only a number and a name over one have a place. Every other type answers null for every value,
 * and the order of such a collection stays the order of its text.
 */
public final class ValuePlaces {

    private static final ValuePlaces NONE = new ValuePlaces(List.of(), null);

    private final List<TypeSymbol> worn;
    private final Carrier carrier;

    private ValuePlaces(List<TypeSymbol> worn, Carrier carrier) {
        this.worn = worn;
        this.carrier = carrier;
    }

    /** What a position of {@code type} places its values by, or nothing where it places none. */
    public static ValuePlaces of(Type type, NewtypeInners inners, Symbols symbols,
                                 DeclarationKinds kinds, SumCases sums) {
        if (type == null) {
            return NONE;
        }
        TypeView view = TypeView.of(type, inners, symbols, kinds, sums);
        Carrier carrier = view.shape() instanceof Shape.Scalar scalar
                ? Carrier.ofPrimitive(scalar.prim())
                : null;
        return carrier instanceof Carrier.Whole || carrier instanceof Carrier.Dense
                ? new ValuePlaces(view.wrappers(), carrier)
                : NONE;
    }

    /** Where an observed value sits, or null where it is not a value of this position's order. */
    public Place of(ObservedValue value) {
        if (carrier == null) {
            return null;
        }
        ObservedValue inside = ObservedValue.wearing(worn, value);
        return inside == null ? null : carrier.placeOf(inside);
    }

    /**
     * Where a stated value sits, or null where it is not a value of this position's order.
     *
     * <p>A name is taken off only where the position wears it and the text built that name over
     * exactly one part, so a record that happens to hold a {@code value} field is not a name over
     * its number.
     */
    public Place of(Asserted value) {
        if (carrier == null) {
            return null;
        }
        Asserted at = value;
        for (TypeSymbol name : worn) {
            if (!(at instanceof Asserted.Built built) || !name.equals(built.type())
                    || !built.fields().keySet().equals(Set.of("value"))) {
                return null;
            }
            at = built.fields().get("value");
        }
        return at instanceof Asserted.Value(ObservedValue bare) ? carrier.placeOf(bare) : null;
    }
}
