package souther.compiler.check;

import souther.compiler.numeric.Place;
import souther.compiler.observe.Asserted;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.List;

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
 *
 * <p>What the position is is read when the first value is asked about, so a collection with nothing
 * to put in order never costs the walk of the names. One of these is made for one collection and
 * read by one thread.
 */
public final class ValuePlaces {

    private final Type type;
    private final NewtypeInners inners;
    private final Symbols symbols;
    private final DeclarationKinds kinds;
    private final SumCases sums;

    /** What the position places its values by, read on first use; null until then. */
    private Reading reading;

    private record Reading(List<TypeSymbol> worn, Carrier carrier) {

        static final Reading NOTHING = new Reading(List.of(), null);
    }

    private ValuePlaces(Type type, NewtypeInners inners, Symbols symbols, DeclarationKinds kinds,
                        SumCases sums) {
        this.type = type;
        this.inners = inners;
        this.symbols = symbols;
        this.kinds = kinds;
        this.sums = sums;
    }

    /** What a position of {@code type}, null where nothing declares it, places its values by. */
    public static ValuePlaces of(Type type, NewtypeInners inners, Symbols symbols,
                                 DeclarationKinds kinds, SumCases sums) {
        return new ValuePlaces(type, inners, symbols, kinds, sums);
    }

    private Reading reading() {
        if (reading == null) {
            reading = read();
        }
        return reading;
    }

    private Reading read() {
        if (type == null) {
            return Reading.NOTHING;
        }
        TypeView view = TypeView.of(type, inners, symbols, kinds, sums);
        Carrier carrier = view.shape() instanceof Shape.Scalar scalar
                ? Carrier.ofPrimitive(scalar.prim())
                : null;
        return carrier instanceof Carrier.Whole || carrier instanceof Carrier.Dense
                ? new Reading(view.wrappers(), carrier)
                : Reading.NOTHING;
    }

    /** Where an observed value sits, or null where it is not a value of this position's order. */
    public Place of(ObservedValue value) {
        Reading at = reading();
        if (at.carrier() == null) {
            return null;
        }
        ObservedValue inside = ObservedValue.wearing(at.worn(), value);
        return inside == null ? null : at.carrier().placeOf(inside);
    }

    /**
     * Where a stated value sits, or null where it is not a value of this position's order.
     *
     * <p>A name is taken off only where the position wears it and the text built that name over
     * exactly one part, which is what a newtype is. A record that happens to be built under another
     * name, or with more parts, is not a name over its number.
     */
    public Place of(Asserted value) {
        Reading at = reading();
        if (at.carrier() == null) {
            return null;
        }
        Asserted inside = value;
        for (TypeSymbol name : at.worn()) {
            if (!(inside instanceof Asserted.Built built) || !name.equals(built.type())
                    || built.fields().size() != 1) {
                return null;
            }
            inside = built.fields().values().iterator().next();
        }
        return inside instanceof Asserted.Value(ObservedValue bare) ? at.carrier().placeOf(bare) : null;
    }
}
