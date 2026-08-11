package souther.compiler.check;

import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.Set;

/**
 * The standard-library operations whose result is a number taken of a location.
 *
 * <p>One list, because a reader that answers "does this rule bound a number" has to give the same
 * answer wherever it is asked. The discharge procedure keys an atom on one of them over its
 * argument's path and a partition draws a boundary on one — and where those two disagreed, a rule
 * discharged in one place was reported in the other as a rule the model does not state, which is
 * what #510 was.
 *
 * <p>Which measure a value has is here as well, beside the list. A partition reading an invariant
 * asks what counts the value in front of it, and a partition reading a guard asks whether the call
 * written there is one of these; answered from two places, adding a measure would be read by one of
 * them and not the other — the same drift one size down.
 *
 * <p>Not what the codec reads. {@code InvariantConstraints} maps a clause onto a decoder constraint,
 * which is a question about what Raoh can enforce rather than about what is a number: it has no
 * entry for {@code Set.size}, because a set crosses the boundary as a list and a constraint chained
 * after the mapping that drops duplicates would count the wrong things. That absence is a fact about
 * the decoder and would be wrong to take from here.
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

    /**
     * Whether the operation counts things no two of which are alike.
     *
     * <p>Here with the rest because it is the same question one step on: what a value of this type
     * is counted by, and what that count is capped at. A count of distinct things is capped by how
     * many there are to be distinct — a {@code Set<Bool>} holds two and no rule makes it hold three
     * — while a length counts positions, and a position is always to be had: a list repeats an
     * element and a string repeats a character.
     *
     * <p>Which is the one thing a range cannot answer. The rules leave a count of three whether or
     * not three of the thing exist, so a reader treating the range as a proof that a value of that
     * count can be written has to know which of these it is looking at.
     */
    public static boolean countsDistinct(ValueName operation) {
        return operation.equals(ValueName.Stdlib.operation("Set", "size"))
                || operation.equals(ValueName.Stdlib.operation("Map", "size"));
    }

    /**
     * The operation that counts what a value of {@code type} holds, or null where nothing counts it.
     *
     * <p>Which one it is follows from what the value is, so a rule read off a declaration and an
     * observation read off a row cannot disagree about which count was meant. Reaches through as
     * many newtypes as the type is written with: a name wrapped round a list is still a list.
     */
    public static ValueName.Stdlib takenOf(Type type, Symbols symbols) {
        Type carried = TypeOps.base(type, symbols);
        if (carried == Type.STRING) {
            return ValueName.Stdlib.operation("String", "length");
        }
        if (carried instanceof Type.ListOf) {
            return ValueName.Stdlib.operation("List", "length");
        }
        if (carried instanceof Type.SetOf) {
            return ValueName.Stdlib.operation("Set", "size");
        }
        if (carried instanceof Type.MapOf) {
            return ValueName.Stdlib.operation("Map", "size");
        }
        return null;
    }

    private NumericMeasures() {}
}
