package souther.compiler.inputs;

import souther.compiler.check.Shape;
import souther.compiler.inputs.BlockReason;
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
 * <p><b>{@link Blocked} is not a conclusion either.</b> It is the reason this position would be
 * left with if nothing else answered for it, and something else still might: a bare
 * {@code List<Item>} cannot have its elements reached, and a {@code guard List.length(items) < 3}
 * draws a line on that same position all the same. So a block is a pending position carrying a
 * fallback, exactly as a leaf is a pending position carrying none, and the two differ only in what
 * is reported when the phases after this one find nothing.
 *
 * <p>{@link Children} is the one answer that is not pending, and that asymmetry is the existing
 * semantics rather than an oversight: a position made of positions is given up in favour of what is
 * under it, before any rule a body writes has been read. Which is why the evidence that decides a
 * descent and the evidence that completes an axis are not the same set.
 */
public sealed interface StructuralInspection {

    /**
     * The answers that leave the position standing.
     *
     * <p>Named because what happens next depends on it and nothing else: a position still to be
     * answered for goes on to the rules a body writes, and a position made of positions is given up
     * in favour of what is under it. Read as "not {@link Children}", the two arms of that were a
     * condition anybody could get the wrong way round — and getting it wrong the quiet way turns a
     * position nothing has read into one nothing divides.
     */
    sealed interface Pending extends StructuralInspection permits Leaf, Blocked, Inside {}

    /**
     * The position is not made of positions.
     *
     * <p>Says that and only that. Whether it divides is still open — the rules a body writes have
     * not been read — so this is a position still to be answered for, and what it becomes if
     * nothing answers is an absence. Reading it as one here puts back the defect the protocol
     * removes.
     */
    record Leaf() implements Pending {}

    /**
     * The position holds values of {@code element}, each of which is read the same way, at the one
     * position they share.
     *
     * <p><b>Pending, unlike {@link Children}.</b> A position made of fields is given up in favour of
     * them, because a record states nothing of its own and carries no end. A sequence is not that: a
     * {@code guard List.length(items) < 3} draws a line on the list itself, and the elements are read
     * beside it rather than instead of it. So this is a position still to be answered for, and the
     * walk goes on down as well — the two are not alternatives, which is the case the other two arms
     * had no room for.
     *
     * <p>One position for however many the list holds, and the coordinate says no more than that
     * ({@link TermPath.Step.Element}). What is written about the elements is written once, so what is
     * read of them is read once; how many of them a row has to put in a class is settled where the
     * class is and not here.
     *
     * @param element what the sequence holds, as the signature wrote it
     */
    record Inside(Type element) implements Pending {}

    /**
     * The position is made of these, each of which is read the same way — in the order the
     * declaration writes them, which is the order they are walked and reported in.
     *
     * <p>The descent's answer as it stands, rather than the fields taken out of it and put into a
     * value of this reading's own. What is under a type is {@link StructuralDescent}'s to say, and
     * unpacking its answer to repackage it leaves two values of one fact where the point of asking
     * one owner was to have one.
     */
    record Children(StructuralDescent.Children descent) implements StructuralInspection {

        /** The fields, as the descent answered them. */
        Map<String, Type> under() {
            return descent.under();
        }
    }

    /**
     * The continuation under the position was not made, and why.
     *
     * <p>Not one reason but three kinds of reason, and they are not the same claim about the model.
     * A traversal this compiler cannot express and a type it could not interpret say something about
     * what is there; a {@link BlockReason.DepthLimit} says only that <em>this reader</em> stopped
     * here, and a reader that goes further finds the positions it declined to look at. Read as "the
     * model puts nothing reachable under this position", the third is a claim nobody made — and it
     * is the one that had a second walk built beside this one, because everything past the reading's
     * depth looked unreachable rather than unasked.
     *
     * <p>{@code why} is the reason this position is left with if nothing else answers for it, not a
     * verdict. A rule a body writes may still draw a line on this same position — a length, a size
     * — and where one does, that is what the position is measured at and this reason is never
     * reported. What it does not do is let a rule about what is <em>inside</em> stand in for
     * reaching inside.
     */
    record Blocked(BlockReason.AboutThePosition why) implements Pending {}

    /**
     * What is under {@code shape}, or why nothing can be.
     *
     * <p>Exhaustive over the shapes a position can have, with no {@code default}. Every one is
     * answered here, so a shape admitted later is a compile error rather than a position that
     * quietly has nothing under it.
     *
     * @param shape   the position's shape, already proved to be one a partition is derived from
     * @param deeper  whether this reading goes on down, which only a position made of positions can
     *                be stopped by. The reading's own answer and not the type's: how far a report is
     *                about one input is what it settles, and a reader that wants what is under a
     *                position this stopped at asks {@link StructuralDescent} rather than being told
     *                there is nothing there
     */
    static StructuralInspection of(Shape.ReadablePositionShape shape, boolean deeper) {
        return switch (shape) {
            // Made of positions, and read one level down — unless this reading stops here, which is
            // a reading that declines to look rather than a record with nothing in it.
            case Shape.Product product -> deeper
                    ? new Children(StructuralDescent.of(product))
                    : new Blocked(new BlockReason.DepthLimit());
            // What a sequence holds is one position, reached whether or not this reading stops
            // here — and the sequence goes on standing either way, since its own length is a number
            // rules are written about.
            case Shape.Sequence sequence -> deeper
                    ? new Inside(sequence.element())
                    : new Blocked(new BlockReason.DepthLimit());
            // Still held inside something nothing here reaches into. Which reaching is missing is
            // kept apart, because what would lift each is different work.
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
