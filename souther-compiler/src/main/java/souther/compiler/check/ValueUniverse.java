package souther.compiler.check;

import souther.compiler.types.Type;
import souther.compiler.values.Value;

import java.util.ArrayList;
import java.util.List;

/**
 * Every value a type has, where they can be counted out at all.
 *
 * <p>Asked so that a rule saying which values a position may not hold can be read as the values it
 * may. {@code /= true} beside {@code /= false} leaves nothing where the values are two and leaves
 * almost everything where they are strings, and the whole of that difference is this answer.
 *
 * <p>Not {@link Carrier}, which answers whether a position has an order-preserving count. The two
 * questions come apart at both ends: a boolean has no order and has two values, a string has an
 * order and has no end of them. Answered with the carrier, a boolean was a position nothing could
 * be counted of.
 *
 * <p>Exhaustive over the primitives, so one added to the language is answered here rather than
 * falling to whichever arm this happened to end with. Where the values cannot be counted out the
 * answer is nothing at all, which is what leaves a rule about them saying only what it excludes.
 */
final class ValueUniverse {

    private ValueUniverse() {}

    /**
     * The values of {@code type} in the order the model writes them, or null where they are not
     * something this counts out.
     *
     * <p>Read through whatever names the type wears: a name wrapped round a boolean is two values
     * like the boolean it wraps.
     */
    static List<Value> of(Type type, Symbols symbols) {
        Type base = TypeOps.base(type, symbols);
        if (base instanceof Type.Prim prim) {
            return switch (prim) {
                case BOOL -> List.of(Value.truth(false), Value.truth(true));
                // Counted out by nobody here. An `Int` and a `Date` have ends rather than a list of
                // values, and what a rule leaves between two of them is read as an interval; a
                // `String`, a `Decimal` and the rest have no end of values between any two. Both
                // are the same answer to this question, which is about writing the values down.
                case INT, DECIMAL, STRING, DATE, TIME, DATETIME, INSTANT, RAW -> null;
            };
        }
        // An enumeration's cases, taken from the one reading that decides which sums are
        // enumerations and in which order their cases stand. A second reading of that here would be
        // a second answer to keep in step with it.
        if (!(Carrier.ofValue(base, symbols) instanceof Carrier.Ordinal ordinal)) {
            return null;
        }
        List<Value> values = new ArrayList<>();
        ordinal.cases().forEach(each -> values.add(Value.of(each)));
        return List.copyOf(values);
    }
}
