package souther.compiler.partition;

import souther.compiler.check.Shape;
import souther.compiler.types.Type;

import java.util.Map;

/**
 * Whether a position is made of positions, asked after the position itself has been read.
 *
 * <p><b>A continuation and not a classifier.</b> The derivation reads what a position's own type
 * says first — the classes it divides into, the ends its rules put on it — and only where that says
 * nothing does it ask what is under the position. So this is reached after local evidence is
 * exhausted, never instead of it, and an answer here says nothing about what the local reading
 * found. A {@code Sum} answers {@link Leaf}, and a {@code Sum} is the position most likely to have
 * had classes: the answer means the sum is not made of positions, not that nothing divides it.
 *
 * <p><b>{@link Leaf} is not an absence.</b> It says there is no structural continuation and nothing
 * else. Whether the position divides is still open when one comes back, because the rules a
 * behavior's body writes have not been read yet — a bare {@code List<String>} nothing bounds is a
 * leaf until a {@code guard List.length(t.names) > 0} draws a line on it. Nothing here may be
 * turned into a report of a position the model does not divide; that conclusion needs the phases
 * after this one to have finished too.
 *
 * <p>{@link Blocked} is not open in the same way, and the asymmetry is the point. What stops a
 * derivation here is a reaching this compiler cannot make or a type it could not interpret, and no
 * rule written in a body lifts either. A threshold inside a list is the reason the elements would
 * have to be reached, not a way of not having to reach them.
 */
public sealed interface StructuralInspection {

    /**
     * The position is not made of positions.
     *
     * <p>Says that and only that. See the type's own note: this is not "no axis can be derived",
     * and reading it as one puts back the defect the whole protocol removes.
     */
    record Leaf() implements StructuralInspection {}

    /** The position is made of these, each of which is read the same way. */
    record Children(Map<String, Type> under) implements StructuralInspection {
        public Children {
            under = Map.copyOf(under);
        }
    }

    /** The derivation stopped, and {@code why} is what stopped it. Terminal: nothing read later
     *  lifts any of these. */
    record Blocked(BlockReason why) implements StructuralInspection {}

    /**
     * What is under {@code shape}, or why nothing can be.
     *
     * <p>Exhaustive over the shapes a position can have, with no {@code default}. Every one is
     * answered here, so a shape admitted later is a compile error rather than a position that
     * quietly has nothing under it.
     *
     * @param shape   the position's shape, already proved to be one a partition is derived from
     * @param deeper  whether the walk may still go down, which only a position made of positions
     *                can be stopped by
     */
    static StructuralInspection of(Shape.PartitionInputShape shape, boolean deeper) {
        return switch (shape) {
            // Made of positions, and read one level down — unless the walk has gone as deep as it
            // goes, which is a reaching this compiler declines rather than a record with nothing in
            // it.
            case Shape.Product product -> deeper ? new Children(product.fields())
                    : new Blocked(new BlockReason.DepthLimit());
            // Holds its values inside something. Which reaching is missing is kept apart, because
            // what would lift each is different work.
            case Shape.Sequence _ ->
                    new Blocked(new BlockReason.UnsupportedTraversal(
                            BlockReason.Traversal.SEQUENCE_ELEMENT));
            case Shape.Optional _ ->
                    new Blocked(new BlockReason.UnsupportedTraversal(
                            BlockReason.Traversal.OPTIONAL_VALUE));
            case Shape.Mapping _ ->
                    new Blocked(new BlockReason.UnsupportedTraversal(
                            BlockReason.Traversal.MAPPING_CONTENT));
            // Nothing was interpreted, so there is nothing to be made of. A model carrying one
            // compiles, which is why this is answered rather than refused.
            case Shape.Unresolved _ -> new Blocked(new BlockReason.TypeUnresolved());
            // Not made of positions. A value of one of these is one value — which is a different
            // statement from the position having no classes, and this makes neither.
            case Shape.Scalar _, Shape.Unit _, Shape.Sum _ -> new Leaf();
        };
    }
}
