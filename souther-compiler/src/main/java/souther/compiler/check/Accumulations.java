package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.semantics.Accumulation;
import souther.compiler.semantics.ArgumentRef;
import souther.compiler.semantics.OperationFacts;
import souther.compiler.types.ValueName;

import java.util.Set;

/**
 * What a call to an accumulating operation walks, for a reader holding the call.
 *
 * <p>A reading and not a table. Which operations accumulate, and what walking one comes to, is a
 * proposition about the operation and is declared with the rest of them
 * ({@link OperationFacts#accumulation}); what is here is the part that depends on having a call in
 * hand — which of its arguments holds the elements. Held as a table of its own, the same operation
 * was stated twice as soon as a second reader wanted it, which is the shape every list of
 * operations in this compiler has already been through once.
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
        return OperationFacts.accumulation(operation);
    }

    /**
     * What {@code call} accumulates and over what, or null where it accumulates nothing.
     *
     * <p>Which argument holds the elements is the fact's to name, and finding it in this call is
     * this method's. Worked out here from the signature instead — the argument whose elements are
     * of the type the operation answers — a signature that fits twice would have to be refused
     * somewhere, and the declaration already says which one it walks.
     */
    static Accumulating accumulating(Core.PreservedCall call) {
        Accumulation what = of(call.operation());
        ArgumentRef container = OperationFacts.accumulatedContainer(call.operation());
        if (what == null || container == null) {
            return null;
        }
        int at = CallArguments.positionIn(container, call.operation());
        return at < 0 || at >= call.args().size() ? null
                : new Accumulating(what, call.args().get(at));
    }

    /** The operations there is a rule about, for the check that a rule answers a question its
     * operation is asked. */
    static Set<ValueName> answered() {
        return OperationFacts.accumulates();
    }

    private Accumulations() {}
}
