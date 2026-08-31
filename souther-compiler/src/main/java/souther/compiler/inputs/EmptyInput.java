package souther.compiler.inputs;

import souther.compiler.check.Emptiness;
import souther.compiler.numeric.Count;

/**
 * Why the rules of a behavior's input leave no value, in the words a caller here already has.
 *
 * <p><b>A proof, and the absence of one is not the opposite.</b> Nothing here says a value exists:
 * where no proof is held, none was found, which is what a search that has not finished looks like as
 * much as what a satisfiable system looks like. A reader that took an empty answer for "there is a
 * value" would be reading a fact about this compiler as a fact about the model.
 *
 * <p><b>Two kinds of fact and not two proofs of one.</b> A caller may fix a position at something no
 * value of it is, which is about the assignment and reads nothing; and the rules taken together may
 * leave no value at all, which is about the rules and reads them. Keeping them apart is the point of
 * this type: put into one proof, a reader could not tell a model that cannot be satisfied from a
 * model that can be, asked about somewhere nothing stands.
 *
 * <p>Nothing here translates. What the rules leave is proved over this input's own subjects, and the
 * places that proof names are this input's places, so it crosses no boundary and is carried as it
 * was written. This was once the seam where a proof about one value's positions was re-spelled into
 * a path of the input — which is a thing to get wrong once per proof, and a thing nobody has to do
 * now that the rules of every parameter are said together under names this input can spell.
 */
public sealed interface EmptyInput {

    /**
     * One position was fixed at two values.
     *
     * <p>A position holds one value, so a caller that fixed it twice fixed it at nothing. Proved
     * here rather than by reading the declarations again: what contradicts is the pair of
     * assignments, and the rules were never asked.
     */
    record TwoValuesAtOnePosition(NumericTerm term, Count one, Count other) implements EmptyInput {}

    /**
     * One position was asked to be two cases.
     *
     * <p>Beside {@link TwoValuesAtOnePosition} and the same kind of fact: what contradicts is what
     * the caller said, and the declarations were never asked. A position holds one value, so a
     * value that is a {@code GlobalQuery} is not also a {@code FeedQuery}, and something fixed under
     * each of them is fixed in no row.
     *
     * <p>Refinements and not cases, because a sum's cases and an optional's presence are narrowings
     * of one kind ({@link Refinement}) — read as cases, the same contradiction under an optional
     * would arrive as a shape of its own with nothing to be an instance of.
     */
    record TwoRefinementsAtOnePosition(TermPath at, Refinement one, Refinement other)
            implements EmptyInput {}

    /**
     * A position was fixed at a value the term itself cannot take.
     *
     * <p>Against what the term guarantees of its own values and against nothing else, which is the
     * whole of what fixing settles without reading anything. A count is never negative and no clause
     * writes that down, so this is what refuses a count fixed below none — and everything the
     * declarations refuse is theirs to refuse, where they are read, which is why a value outside a
     * declared bound arrives as {@link ProvedByTheRules} instead.
     *
     * <p>The place is the term's own and is not said again beside it. A term is a position, so a
     * proof carrying a path of its own here would be one fact in two spellings, free to disagree.
     */
    record OutsideWhereThePositionRuns(NumericTerm term, Count fixed) implements EmptyInput {}

    /**
     * The rules of every parameter and everything a caller took in, said together, leave no value.
     *
     * <p>One proof and one prover. Every parameter's reading is in the space this was proved over,
     * so there is no second reading with an answer of its own to compare against — which is what
     * used to make the report depend on which of two provers was asked first.
     *
     * @param why what was shown, and where it sits when the proof can name a place. Carried as it
     *            was proved: the subjects it is about are this input's, so its places are already
     *            spelled the way a caller here spells them
     */
    record ProvedByTheRules(Emptiness why) implements EmptyInput {

        public ProvedByTheRules {
            if (why == null) {
                throw new IllegalArgumentException("an emptiness is the proof of one");
            }
        }
    }
}
