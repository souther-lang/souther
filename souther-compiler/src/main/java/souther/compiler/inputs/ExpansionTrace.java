package souther.compiler.inputs;

import souther.compiler.check.Shape;
import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Which declarations are open above a position, and where each of them was entered.
 *
 * <p>What makes the walk over an input finite. A declaration's fields are read by opening the
 * declaration, so a path that opens one already open on it would go on opening it: a tree
 * {@code data Node = { kids: List<Node> }} compiles, is constructible, and has an input path for
 * every depth. The walk stops where it would enter {@code Node} a second time, and that is the
 * whole of what stops it — no count of steps is kept, so how deep an author nests a value decides
 * nothing about whether it is read.
 *
 * <p><b>The ancestors of one path and not everywhere the walk has been.</b> Two fields of one record
 * declared as the same type are two positions and both are read; the same type reached twice down
 * one path is the path returning to where it was. Held as one set for the whole walk, the second
 * sibling would be reported as a recursion, and a model with two addresses in it would have one of
 * them measured. So this is handed down a branch and never back up, and a branch that ends takes its
 * entries with it.
 *
 * <p>Where each declaration was entered is kept beside it, because what is said at the position that
 * stops is that the input returns to somewhere it has already been, and a reader wanting to see the
 * cycle needs both ends of it.
 */
public record ExpansionTrace(Map<TypeSymbol, TermPath> open) {

    /** Nothing open: what a parameter's own position is read under. */
    public static final ExpansionTrace NONE = new ExpansionTrace(Map.of());

    public ExpansionTrace {
        open = Map.copyOf(open);
    }

    /**
     * The declaration reading what is under {@code shape} would open, or null where reading on
     * opens none.
     *
     * <p>Exhaustive over the shapes a position has, with no {@code default}, so a shape admitted
     * later is answered here rather than walked as one that opens nothing — which is the answer
     * that does not terminate.
     *
     * <p>A sequence and an optional open nothing. What a list holds and what an option holds are
     * types in their own right and are declared elsewhere or nowhere; the position under them is
     * where the declaration they name is opened, and it is that position this is asked of.
     */
    public static TypeSymbol unfoldedBy(Shape.ReadablePositionShape shape) {
        return switch (shape) {
            // Its fields are read by opening it, and its fields are what may name it again.
            case Shape.Product product -> product.name();
            // Its cases are entered by opening it, and a case may carry the sum back.
            case Shape.Sum sum -> sum.name();
            case Shape.Sequence _, Shape.Optional _, Shape.Mapping _, Shape.Scalar _,
                 Shape.Unit _, Shape.Unresolved _ -> null;
        };
    }

    /**
     * Where {@code declaration} was opened above this position, or null where it is not open.
     *
     * <p>Answers null for a position that opens no declaration, so a caller asks this of whatever
     * {@link #unfoldedBy} gave it rather than deciding first whether there is anything to ask
     * about.
     */
    public TermPath openedAt(TypeSymbol declaration) {
        return declaration == null ? null : open.get(declaration);
    }

    /**
     * The same trace with {@code declaration} open at {@code at}, or this one where there is nothing
     * to add.
     *
     * <p>Only ever called where {@link #openedAt} answered null, so an entry is never replaced: the
     * first position a declaration was opened at is the one the cycle is reported against, and
     * overwriting it would move the far end of the cycle to wherever the walk happened to be last.
     */
    public ExpansionTrace opening(TypeSymbol declaration, TermPath at) {
        if (declaration == null) {
            return this;
        }
        Map<TypeSymbol, TermPath> deeper = new LinkedHashMap<>(open);
        deeper.put(declaration, at);
        return new ExpansionTrace(deeper);
    }
}
