package souther.compiler.partition;

import souther.compiler.inputs.TermPath;
import souther.compiler.values.ValueSet;

/**
 * What the declarations leave each position of an input, for a search that is about to compose a
 * value at one of them.
 *
 * <p>Apart from the region a search runs inside. That one is arithmetic — the runs the rules leave
 * each number, met as positions are fixed — and this is the set of values a position holds, which
 * the arithmetic has no word for: a rule about the length of a string says nothing about where the
 * string sorts, so a search held to the run of one number can still arrive at a value the
 * declarations refuse. Kept as one input beside the other, neither is asked the other's question.
 *
 * <p>Keyed by the position and not by the number. {@code code} and {@code String.length(code)} are
 * two numbers of one location, and what that location admits is one answer — held per number, the
 * same answer would be copied once per measure and two copies could disagree. Which is why the key
 * is {@link souther.compiler.inputs.NumericTerm.FromOnePosition#position()}, the location a value
 * answering the number is written at.
 *
 * <p><b>Three states and not two.</b> A position whose rules leave it everything is one this answers
 * for, with every value there is. A position this measurement has no set for is a different thing,
 * and saying so is the whole of what this does about it: a caller told "everything" would be told
 * the declarations leave a position what nothing worked out, which is the defect this exists to
 * stop, moved behind a lookup.
 *
 * <p><b>What a search does about that is not stated here.</b> It differs with the question: one
 * asked whether a region admits an assignment has no set to narrow by, and one composing a value to
 * write into a row has nothing to compose from. Both are right and neither is this type's to
 * choose, so the two are named where a search is handed what it searches with
 * ({@link WitnessSearch#toNarrowBy}, {@link WitnessSearch#toComposeFrom}). Said here as one action,
 * whichever search was written first would have its answer applied to the other.
 *
 * <p>And the third state covers more than a reading that stopped. A name deeper than the positions
 * a reading divided reaches it ({@code o.q@B.q.limit} under a choice whose cases were never filed),
 * and so does a name that is no position of this reading at all — every case of a sum spreading one
 * field puts the reading under each case, so the shared name has no position to have been worked
 * out. The two are not one fact and this does not tell them apart.
 */
public interface AdmittedValues {

    /** What the declarations leave the position at {@code position}, or that nothing worked it out. */
    Admitted at(TermPath position);

    /**
     * What a reading came to about one position's values.
     *
     * <p>Two cases, because a set and the absence of one are not one thing with a value standing in
     * for the other. What a caller may do with them differs: a set narrows the search, and nothing
     * worked out narrows nothing and licenses nothing either — a value composed against it would be a
     * value offered at a position whose rules this compiler never read.
     */
    sealed interface Admitted {

        /** The values the declarations leave, which is every value where no rule narrows them. */
        record Values(ValueSet set) implements Admitted {

            public Values {
                if (set == null) {
                    throw new IllegalArgumentException(
                            "a position that was read holds a set, and a position that was not is"
                                    + " NotWorkedOut rather than one holding null");
                }
            }
        }

        /**
         * Nothing here worked out what the position holds.
         *
         * <p>A fact about this reading and not about the model, and that is the whole of what it
         * says. Read as a set of every value, it would be the declarations answering for a position
         * they were never asked about.
         *
         * <p>What follows for a search is the search's question and is settled where a search is
         * handed what it searches with ({@link WitnessSearch}). One that narrows by sets has none
         * to narrow by here; one that composes a value to write has nothing to compose from. A
         * single answer written here would be whichever of the two was needed first.
         */
        record NotWorkedOut() implements Admitted {}
    }

    /**
     * What a reading of an input leaves its positions, from the sets it already answered with.
     *
     * <p>The sets are handed in rather than read out of a reading here. What a position admits is
     * settled once, where the declarations are read, and a second route to it is a second answer
     * about the model — including for a position this one has no entry for, which is why that comes
     * back as nothing worked out rather than being worked out again from the path.
     *
     * @param byPosition the set each position the reading divided was read to leave, a position whose
     *                   rules leave it everything included
     */
    static AdmittedValues of(java.util.Map<TermPath, ValueSet> byPosition) {
        java.util.Map<TermPath, ValueSet> sets = java.util.Map.copyOf(byPosition);
        return position -> {
            ValueSet held = sets.get(position);
            return held == null ? new Admitted.NotWorkedOut() : new Admitted.Values(held);
        };
    }
}
