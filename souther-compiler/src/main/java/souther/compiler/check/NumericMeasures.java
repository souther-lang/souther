package souther.compiler.check;

import souther.compiler.types.ValueName;

import java.util.Set;

/**
 * The standard-library operations whose result is a number taken of a location.
 *
 * <p>One list, because every reader of a model that has to know which calls these are has to agree
 * about it. The discharge procedure keys an atom on one of them over its argument's path, the codec
 * turns one into a decoder's length constraint, and a partition draws a boundary on one — and a
 * model where two of those disagreed would enforce a rule at the boundary that the report says the
 * model does not state.
 *
 * <p>Held as the names they resolve to rather than as spellings. Two ways of writing a call that
 * reach one operation are one operation, and comparing {@code "String.length"} against a rendering
 * is reading a name back out of its text.
 */
public final class NumericMeasures {

    private static final Set<ValueName> CALLS = Set.of(
            ValueName.Stdlib.operation("List", "length"),
            ValueName.Stdlib.operation("String", "length"),
            ValueName.Stdlib.operation("Set", "size"),
            ValueName.Stdlib.operation("Map", "size"));

    /** Every such operation. */
    public static Set<ValueName> calls() {
        return CALLS;
    }

    /** Whether {@code operation} is one of them. */
    public static boolean isMeasure(ValueName operation) {
        return CALLS.contains(operation);
    }

    private NumericMeasures() {}
}
