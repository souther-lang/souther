package souther.compiler.check;

import souther.compiler.types.ValueName;

/**
 * One number, at one place: which of the numbers there it is, and where it sits.
 *
 * <p><b>A subject and not a proposition.</b> Nothing here says a rule was written about this
 * number, or that anything is owed at it, or that a line falls on it. Every producer makes one of
 * these from what is at a place: the values a caller settled, the atoms a reading has names for,
 * the count a shape declares, the number an axis measures. A name saying a rule claims something
 * would have been true of a few of them and asserted of all — and the reader who came next would
 * take the assertion for a guarantee. Whether a question stands about this number is what
 * {@link Owed.Boundary} and {@code inputs.InputQuestion.AboutANumber} say, in the arm, where it can
 * be true of everything that reaches it.
 *
 * <p><b>What it is made of takes no reading.</b> The place is what a vocabulary calls it, and the
 * operation is a resolved name — the one the shape declares its values are measured by
 * ({@code NumericMeasures.takenOf}), or the one a call in the source resolved to
 * ({@code inputs.NumericTerm.TakenOf}), which are two ways to the same name and not two provenances
 * a reader has to tell apart. So one of these exists for a rule this compiler has not read and
 * cannot read. That is what lets a question be asked about a number nothing could be made of: held
 * as a term instead ({@link souther.compiler.inputs.NumericTerm}), the question could only be
 * stated where the reading had already succeeded, and the shortfall was left to be carried in a
 * list beside the accounting.
 *
 * <p><b>The place is a parameter because it crosses a boundary and the number does not.</b> A
 * reading of a declaration knows its places by a key relative to the value the clauses are written
 * on; an input is walked by a path from a parameter. One of these is the other with the place
 * written the other way, which is what {@link #at} does and the whole of what the crossing is. The
 * operation is the same value on both sides, so nothing about it is translated and nothing about it
 * can be lost.
 *
 * <p><b>What stands at a place is not always a number.</b> A string is bounded on its order and
 * admits a set of values and is at a name like anything else, and a caller that has to say what two
 * readings of one name came to needs them under the one subject whichever of the two the rules
 * happened to reach. So this says where a subject sits and which of the numbers there it is, and a
 * reader that only has numbers to give finds nothing at a place it takes none of — which is the
 * answer rather than a case to rule out.
 *
 * <p><b>The operation as it resolved, and not as it was written.</b> Two spellings reaching one
 * operation are one subject, and comparing renderings is reading a name back out of its text. What
 * that operation answers, where its number runs and whether this compiler can read it are facts
 * declared elsewhere and asked by whoever answers — never here, because a subject that asked them
 * would exist only for the operations the answer side already handles.
 *
 * @param position where the number is read from
 * @param of       which of the numbers there it is
 */
public record NumberAt<P>(P position, NumberAt.OfWhatNumber of) {

    public NumberAt {
        if (position == null) {
            throw new IllegalArgumentException("a number is somewhere");
        }
        if (of == null) {
            throw new IllegalArgumentException("and is one of the numbers that are there");
        }
    }

    /** What stands at {@code position}. */
    public static <P> NumberAt<P> valueOf(P position) {
        return new NumberAt<>(position, new OfWhatNumber.OfItsOwnValue());
    }

    /** The number {@code operation} answers of what stands at {@code position}. */
    public static <P> NumberAt<P> takenOf(P position, ValueName operation) {
        return new NumberAt<>(position, new OfWhatNumber.OfWhatAnOperationAnswers(operation));
    }

    /**
     * The same number with the place spelled {@code position}.
     *
     * <p>The whole of the crossing between a declaration's vocabulary and an input's. What is
     * translated is the place; which number of it this is stays as it is, so no capability of
     * either side decides whether the subject survives the trip.
     */
    public <Q> NumberAt<Q> at(Q position) {
        return new NumberAt<>(position, of);
    }

    /**
     * Which of the numbers at one place this is.
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
     * over one place are two of these, and "count of" spells them the same.
     *
     * <p>What a document calls one of these is the document's, and every reader that writes one
     * spells the place its own way ({@link Owed}, {@code check.DeclaredBorders.nameOf},
     * {@code query.PartitionEvidence.Unanswered.measure}). So this is for a diagnostic and for
     * reading a value in a debugger: with it changed to something else altogether, every checked-in
     * answer over the corpora still compares equal, which is what says nothing is built out of it.
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
