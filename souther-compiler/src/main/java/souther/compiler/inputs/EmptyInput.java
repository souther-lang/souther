package souther.compiler.inputs;

import souther.compiler.numeric.Count;

/**
 * Why the rules of a behavior's input leave no value, in the words a caller here already has.
 *
 * <p><b>A proof, and the absence of one is not the opposite.</b> Nothing here says a value exists:
 * where no proof is held, none was found, which is what a search that has not finished looks like as
 * much as what a satisfiable system looks like. A reader that took an empty answer for "there is a
 * value" would be reading a fact about this compiler as a fact about the model.
 *
 * <p><b>The one place a proof of emptiness changes vocabulary.</b> What proves it is the reading of
 * the declarations, which names a position the way the declaration does — {@code x} for a field of
 * the record the clause was written on. A caller out here holds {@code p.x}, and the two spellings
 * are the same position or the report names one nobody wrote. So the translation happens where a
 * {@link Quantities} is made and nowhere after it: handed the declaration's proof, every caller
 * would translate it again, and a caller that did not would name a position the model has no such
 * field of.
 */
public sealed interface EmptyInput {

    /**
     * Under one position of the input, and what is under it there.
     *
     * <p>The path is this input's, which is the whole reason this type exists beside the proof the
     * declaration reading holds.
     */
    record At(TermPath path, EmptyInput under) implements EmptyInput {

        public At {
            if (path == null || under == null) {
                throw new IllegalArgumentException("an emptiness under a position names both");
            }
        }
    }

    /**
     * One position was fixed at two values.
     *
     * <p>A position holds one value, so a caller that fixed it twice fixed it at nothing. Proved
     * here rather than by reading the declarations again: what contradicts is the pair of
     * assignments, and the rules were never asked.
     */
    record TwoValuesAtOnePosition(NumericTerm term, Count one, Count other) implements EmptyInput {}

    /**
     * A position was fixed at a value the term itself cannot take.
     *
     * <p>Against what the term guarantees of its own values and against nothing else, which is the
     * whole of what fixing settles without reading anything. A count is never negative and no clause
     * writes that down, so this is what refuses a count fixed below none — and everything the
     * declarations refuse is theirs to refuse, where they are read, which is why a value outside a
     * declared bound arrives as {@link ProvedByTheDeclarationsReading} instead.
     */
    record OutsideWhereThePositionRuns(NumericTerm term, Count fixed) implements EmptyInput {}

    /**
     * The reading of the declarations proved it, at no position this can name.
     *
     * <p>What proved it is that reading's, and how much of its proof is carried across is a question
     * about who reads this. Nothing does yet beyond deciding that a branch is closed, so what
     * crosses is that a proof exists and where in the input it sits, and the rest stays where it was
     * proved. Widening this is one edit, in the translation above.
     */
    record ProvedByTheDeclarationsReading() implements EmptyInput {}
}
