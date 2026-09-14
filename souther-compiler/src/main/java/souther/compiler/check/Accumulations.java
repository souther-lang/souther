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
 * {@link Question#ACCUMULATION} states the range and the declarations answer it.
 */
final class Accumulations {

    /** What a call accumulates, and the container it accumulates over. */
    record Accumulating(Accumulation what, Core container) {}

    /**
     * The operations in range that accumulate from no identity through no single step.
     *
     * <p>{@code String.join} is one, and not because it answers a string. A separator stands between
     * elements and not before the first, so what the walk does at each element depends on whether
     * anything came before it — and an identity with a combine over two values of one type has
     * nowhere to keep that. Written as {@code join(sep, xs)} it is a walk carrying more than the
     * answer so far, which is a different question from this one and is not asked of it here.
     */
    static final Set<ValueName> NO_SIMPLE_ACCUMULATION =
            Set.of(ValueName.Stdlib.operation("String", "join"));

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

    /** The operations there is a rule about, for the check that a rule answers a question its
     * operation is asked. */
    static Set<ValueName> answered() {
        return DefaultBoundOperationFacts.get().accumulates();
    }

    private Accumulations() {}
}
