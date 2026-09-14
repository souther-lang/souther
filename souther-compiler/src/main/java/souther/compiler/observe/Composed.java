package souther.compiler.observe;

import souther.compiler.types.Type;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * What a declaration a module wrote is made of.
 *
 * <p>Two answers and not one answer with a hole in it. A data a value is built out of has fields; a
 * sum and a unit have none, and that is something known about them rather than something missing.
 * A world that cannot say which of the two a declaration is has not answered at all, and says so by
 * refusing rather than by handing back the emptier of the two.
 *
 * <p>Written as a type because the difference is what a reader of a value does next. Carried as an
 * empty map, "nothing is built field by field here" and "this world does not hold that declaration"
 * are the same value — and the second read as the first is a value compared as whatever its parts
 * happen to look like, wherever the declaration that says otherwise was not in hand.
 */
public sealed interface Composed {

    /** A data a value of is built field by field, with what each field holds, in the order a value
     *  of it is laid out. A newtype is one of these: the one field it is written with. */
    record OfFields(Map<String, Type> fields) implements Composed {

        public OfFields {
            // The order is the layout and a reader writing a value's parts out follows it, so what
            // is kept is the order handed over rather than whatever a copy happens to iterate in.
            fields = Collections.unmodifiableMap(new LinkedHashMap<>(fields));
        }
    }

    /** A declaration no value is built field by field out of — a sum, a unit. Nothing stands under
     *  it to be read against a field. */
    record OfNothing() implements Composed {}

    Composed NOTHING = new OfNothing();
}
