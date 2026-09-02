package souther.compiler.check;

import souther.compiler.types.ValueName;

/**
 * What a rule says a line falls on: one number, at one place, named the way the author wrote it.
 *
 * <p><b>What a question is about, and never what a reader made of it.</b> A number the model draws
 * a line on is named by the place it is read from and by the operation that answers it there.
 * Neither takes a reading: the place is what the rules call it and the operation is what the call
 * resolved to, so a claim can be made for a rule this compiler has not read and cannot read. Held
 * as a term instead ({@link souther.compiler.inputs.NumericTerm}), the question could only be
 * stated where the reading had already succeeded — and a rule whose number nothing could be made of
 * raised no question at all, which left the shortfall to be carried in a list beside the accounting.
 *
 * <p><b>The place is a parameter because the question crosses a boundary and the number does
 * not.</b> A reading of a declaration knows its places by a key relative to the value the clauses
 * are written on; an input is walked by a path from a parameter. One claim is the other with the
 * place written the other way, which is what {@link #at} does and the whole of what the crossing
 * is. The operation is the same value on both sides, so nothing about it is translated and nothing
 * about it can be lost.
 *
 * <p><b>What stands at a place is not always a number.</b> A string is bounded on its order and
 * admits a set of values and is at a name like anything else, and a caller that has to say what two
 * readings of one name came to needs them under the one claim whichever of the two the rules
 * happened to reach. So this says where a subject sits and which of the numbers there it is, and a
 * reader that only has numbers to give finds nothing at a place it takes none of — which is the
 * answer rather than a case to rule out.
 *
 * <p><b>The operation as it resolved, and not as it was written.</b> Two spellings reaching one
 * operation are one claim, and comparing renderings is reading a name back out of its text. What
 * that operation answers, where its number runs and whether this compiler can read it are facts
 * declared elsewhere and asked by whoever answers — never here, because a question that asked them
 * would exist only for the operations the answer side already handles.
 *
 * @param position where the number is read from
 * @param of       which of the numbers there it is
 */
public record BoundaryClaim<P>(P position, BoundaryClaim.OfWhatNumber of) {

    public BoundaryClaim {
        if (position == null) {
            throw new IllegalArgumentException("a line falls on a number somewhere");
        }
        if (of == null) {
            throw new IllegalArgumentException("and on one of the numbers that are there");
        }
    }

    /** The line is on what stands at {@code position}. */
    public static <P> BoundaryClaim<P> valueOf(P position) {
        return new BoundaryClaim<>(position, new OfWhatNumber.OfItsOwnValue());
    }

    /** The line is on the number {@code operation} answers of what stands at {@code position}. */
    public static <P> BoundaryClaim<P> takenOf(P position, ValueName operation) {
        return new BoundaryClaim<>(position, new OfWhatNumber.OfWhatAnOperationAnswers(operation));
    }

    /**
     * The same claim with the place spelled {@code position}.
     *
     * <p>The whole of the crossing between a declaration's vocabulary and an input's. What is
     * translated is the place; what the number is stays as it is, so no capability of either side
     * decides whether the claim survives the trip.
     */
    public <Q> BoundaryClaim<Q> at(Q position) {
        return new BoundaryClaim<>(position, of);
    }

    /**
     * Which of the numbers at one place a claim is on.
     *
     * <p>A boolean while a place had two numbers — what stands there and the count taken of it —
     * and the count was the only thing anything ever took. It is not: {@code Int.abs(x)} is a third
     * number at the same place, and told apart by a flag it would arrive as the count of {@code x}
     * and be read against clauses written about how many {@code x} holds. Two numbers coming to one
     * place is what this exists to stop, so what makes them two is carried rather than summarised.
     */
    public sealed interface OfWhatNumber {

        /** What stands at the place. */
        record OfItsOwnValue() implements OfWhatNumber {}

        /** What an operation answers of what stands there. */
        record OfWhatAnOperationAnswers(ValueName operation) implements OfWhatNumber {

            public OfWhatAnOperationAnswers {
                java.util.Objects.requireNonNull(operation, "this one names the operation");
            }
        }
    }

    /**
     * The number, named. The operation and not a word for the kind of thing it is: two operations
     * over one place are two claims, and "count of" spells them the same.
     *
     * <p>What a document calls one of these is the document's, and every reader that writes one
     * spells the place its own way — so this is for a diagnostic and for reading a value in a
     * debugger, and nothing checked in is built out of it.
     */
    @Override
    public String toString() {
        return switch (of) {
            case OfWhatNumber.OfItsOwnValue _ -> position.toString();
            case OfWhatNumber.OfWhatAnOperationAnswers taken ->
                    taken.operation() + "(" + position + ")";
        };
    }
}
