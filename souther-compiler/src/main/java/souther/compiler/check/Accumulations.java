package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.semantics.Accumulation;
import souther.compiler.types.ValueName;

import java.util.Set;

/**
 * What a call to an accumulating operation walks, for a reader holding the call.
 *
 * <p>A reading and not a table. Which operations accumulate, and what walking one comes to, is a
 * proposition about the operation and is declared with the rest of them and read from the binding
 * ({@link BoundOperationFacts#accumulates}); what is here is the part that depends on having a call
 * in hand — the expression standing where the fact says the elements are. Held as a table of its
 * own, the same operation was stated twice as soon as a second reader wanted it, which is the shape
 * every list of operations in this compiler has already been through once.
 *
 * <p>The sibling of {@link Reductions}, and separate for the reason that is separate from
 * {@link Combinators}. A reduction is handed the step it repeats and this is not: {@code List.sum}
 * takes a container and nothing else, so what it starts from and what it repeats are not arguments
 * anything can read off the call — they are what the operation means.
 */
final class Accumulations {

    /** What a call accumulates, and the container it accumulates over. */
    record Accumulating(Accumulation what, Core container) {}

    /** What {@code operation} accumulates, or null where it accumulates nothing. */
    static Accumulation of(ValueName operation) {
        return DefaultBoundOperationFacts.get().accumulation(operation);
    }

    /**
     * What {@code call} accumulates and over what, or null where it accumulates nothing.
     *
     * <p>Which argument holds the elements is the fact's to name and the binder's to place, and
     * finding it in this call is {@link CallArguments}'. Worked out here from the signature instead
     * — the argument whose elements are of the type the operation answers — a signature that fits
     * twice would have to be refused somewhere, and the declaration already says which one it walks.
     */
    static Accumulating accumulating(Core.PreservedCall call) {
        BoundOperationFact.AccumulatesItsContainer walk =
                DefaultBoundOperationFacts.get().accumulates(call.operation());
        return walk == null ? null
                : new Accumulating(walk.how(), CallArguments.of(walk.container(), call));
    }

    /** The operations there is a rule about. */
    static Set<ValueName> answered() {
        return DefaultBoundOperationFacts.get().accumulates();
    }

    private Accumulations() {}
}
