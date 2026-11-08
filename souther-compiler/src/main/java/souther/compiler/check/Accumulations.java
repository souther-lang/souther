package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.semantics.Accumulation;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
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

    /**
     * A fold written out that is a library operation over whole numbers: {@code operation} over
     * {@code container}, which is {@code what} where it accumulates and is the count of its
     * container where {@code what} is null.
     */
    record Spelled(ValueName operation, Accumulation what, Core container) {}

    /** What a fold is written as once the library has put its starting position in. */
    private static final ValueName FOLD = ValueName.Stdlib.operation("List", "foldFrom");

    /**
     * The library operation {@code call} is, where it is a fold of whole numbers from the value
     * the operation starts from by the step the operation repeats: adding what is handed, from
     * nought, is {@code List.sum}; multiplying, from one, is {@code List.product}; adding one, from
     * nought, is how many there are.
     *
     * <p>The same value, so the same term: a reader that took the two for different values would
     * hold what one says of the total against a total it had not been told is the same. Only a
     * step written out in the call, and only over whole numbers — a total of decimals or a step
     * that reads anything but the two it is handed is a fold and nothing more.
     */
    static Spelled spelledOut(Core.PreservedCall call) {
        if (!FOLD.equals(call.operation())) {
            return null;
        }
        Reductions.Reducing walk = Reductions.reducing(call,
                closure -> Core.withoutStanding(closure) instanceof Core.Block block
                        ? block : null);
        if (walk == null || walk.step().params().size() != 2
                || !(Core.withoutStanding(walk.seed()) instanceof Core.Int seed)
                || !(Core.withoutStanding(walk.step().body()) instanceof Core.Binary step)
                || !Type.INT.equals(step.type())) {
            return null;
        }
        BindingId accumulator = walk.accumulator().binding();
        BindingId element = walk.element().binding();
        if (seed.value() == 0 && step.op() == BinOp.ADD && handed(step, accumulator, element)) {
            return new Spelled(ValueName.Stdlib.operation("List", "sum"),
                    new Accumulation(Accumulation.Identity.ZERO, Accumulation.Combine.ADD),
                    walk.container());
        }
        if (seed.value() == 1 && step.op() == BinOp.MUL && handed(step, accumulator, element)) {
            return new Spelled(ValueName.Stdlib.operation("List", "product"),
                    new Accumulation(Accumulation.Identity.ONE, Accumulation.Combine.MULTIPLY),
                    walk.container());
        }
        if (seed.value() == 0 && step.op() == BinOp.ADD
                && (oneMore(step.left(), step.right(), accumulator)
                        || oneMore(step.right(), step.left(), accumulator))) {
            return new Spelled(ValueName.Stdlib.operation("List", "length"), null,
                    walk.container());
        }
        return null;
    }

    /** Whether {@code step} combines the two it is handed, in whichever order. */
    private static boolean handed(Core.Binary step, BindingId accumulator, BindingId element) {
        return (reads(step.left(), accumulator) && reads(step.right(), element))
                || (reads(step.left(), element) && reads(step.right(), accumulator));
    }

    private static boolean oneMore(Core held, Core one, BindingId accumulator) {
        return reads(held, accumulator)
                && Core.withoutStanding(one) instanceof Core.Int literal && literal.value() == 1;
    }

    private static boolean reads(Core value, BindingId binding) {
        return Core.withoutStanding(value) instanceof Core.Read read
                && read.binding().equals(binding);
    }

    /** The operations there is a rule about. */
    static Set<ValueName> answered() {
        return DefaultBoundOperationFacts.get().accumulates();
    }

    private Accumulations() {}
}
