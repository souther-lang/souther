package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.ReachName;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;
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

    /** Every such operation. */
    public static Set<ValueName> calls() {
        return souther.compiler.semantics.OperationFacts.countsWhatItIsGiven();
    }

    /** Whether {@code operation} is one of them. */
    public static boolean isMeasure(ValueName operation) {
        return calls().contains(operation);
    }

    /** One of these applied to something: which measure, and what it is taken of. */
    public record Measured(ValueName.Stdlib operation, Core of) {}

    /**
     * The measure {@code e} takes and what it takes it of, or null where it takes none.
     *
     * <p>Asked here rather than matched on a call's shape, because the same call arrives in two
     * shapes and which of them is not a detail of the walk. The tree that runs holds a
     * language-defined operation as a call of what it resolved to; the tree a declaration's own
     * rules are read in keeps it standing ({@link Core.PreservedCall}). A reader that knew one shape
     * drew the line a {@code guard} puts on a length and not the one a clause puts on the same
     * length — the same drift the list above exists to stop, one representation down.
     *
     * <p>The argument has to be one thing. A measure of several is not one of these, and what it
     * would be counted at is not a place either.
     */
    public static Measured measureIn(Core e) {
        ValueName operation = switch (e) {
            case Core.Call call when call.fn() instanceof Core.Reached reached
                    && reached.name() instanceof ReachName.OfLibrary library ->
                    library.target();
            case Core.PreservedCall preserved -> preserved.operation();
            case null, default -> null;
        };
        List<Core> args = switch (e) {
            case Core.Call call -> call.args();
            case Core.PreservedCall preserved -> preserved.args();
            case null, default -> List.of();
        };
        return operation instanceof ValueName.Stdlib measure && isMeasure(measure)
                && args.size() == 1
                ? new Measured(measure, args.get(0)) : null;
    }

    /**
     * Whether every count this operation could give is a count some value of the type has.
     *
     * <p>Here with the rest because it is the same question one step on: what a value of this type
     * is counted by, and whether the number a rule leaves is a number something holds. Only a
     * string's length is. A string of any length is written by repeating a character and a character
     * is always to be had, so what the rules leave is what some value has.
     *
     * <p>Every other measure counts things that may not be there. A {@code Set<Bool>} is capped at
     * two by how many booleans there are; a {@code List<T>} of one needs a {@code T}, and a
     * {@code T} nothing inhabits has none. Whether such a value exists is a question about the
     * element and not about the count, and the numeric domain has no term for it — so the range is
     * not a proof, and a row at that edge is settled by a value rather than by an argument.
     */
    public static boolean everyCountHasAValue(ValueName operation) {
        return souther.compiler.semantics.OperationFacts
                .everyCountItGivesIsACountSomeValueHas(operation);
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
