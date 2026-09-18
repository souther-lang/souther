package souther.compiler.partition;

import souther.compiler.inputs.NameReach;
import souther.compiler.inputs.TermPath;
import souther.compiler.values.ValueSet;

import java.util.Map;

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
 * <p><b>And a path that is no position at all is the third.</b> Every case of a sum spreading one
 * field puts the reading under each case, so a rule may be written at the sum's own name while the
 * values stand under the cases. Nothing was left short there and there is nothing there to work
 * out — a value written at that name goes under a case, and whatever writes it says whether it can
 * be. Held as one word with a reading that stopped, the two would license the same thing, and the
 * one place the difference shows is where a value is composed.
 *
 * <p><b>What a search does about them is not stated here.</b> It differs with the question: one
 * asked whether a region admits an assignment has no set to narrow by, and one composing a value to
 * write into a row has the run and nothing of this reading's narrowing it. Both are right and
 * neither is this type's to choose, so they are named where a search is handed what it searches
 * with ({@link WitnessSearch#toNarrowBy}, {@link WitnessSearch#toComposeFrom}). Said here as one
 * action, whichever search was written first would have its answer applied to the other.
 */
public interface AdmittedValues {

    /** What the declarations leave the position at {@code position}, where a position is what the
     *  path reaches and the reading answered for it. */
    Admitted at(TermPath position);

    /**
     * What a reading came to about one position's values.
     *
     * <p>Three cases, because a set, a reading short of the position and a path the reading puts no
     * position at are not one thing with a value standing in for the others. What a caller may do
     * with them differs: a set narrows the search; a reading that stopped licenses nothing — a value
     * composed against it would be a value offered at a position whose rules this compiler never
     * read; and a path that is no position of this reading narrows nothing while licensing a value,
     * because what refuses one there is whatever writes it.
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

        /**
         * The path reaches no position of this reading: the values stand under the cases of a sum
         * whose every case spreads the name.
         *
         * <p>A fact about where the language puts a value and not about how far this compiler got.
         * Nothing here was left short — a name the cases share is one a rule of the sum may be
         * written at, and the value answering it is written under whichever case the row turns out
         * to be. So there are no rules of this path to have read, and a value offered at it is
         * refused or not by whatever writes the row.
         *
         * <p>Not the set of every value either. Read as one, this would be the declarations
         * answering that they leave a position everything, and the position is not one they were
         * ever asked about — the two coincide in narrowing nothing and differ in what they say,
         * which is why the coincidence is not written down as the answer.
         */
        record StandsUnderTheCases() implements Admitted {}
    }

    /**
     * What a reading of an input leaves its positions, from the sets it already answered with.
     *
     * <p>The sets are handed in rather than read out of a reading here. What a position admits is
     * settled once, where the declarations are read, and a second route to it is a second answer
     * about the model — including for a position this one has no entry for, which is why that comes
     * back as nothing worked out rather than being worked out again from the path.
     *
     * <p><b>What a lookup misses is sorted here, from what the same walk observed.</b> A miss is a
     * fact about this map and is no answer about anything — the two states it covers are told apart
     * by where the walk saw a name stand, and a caller left to sort them would be deciding it from
     * how a path is spelled.
     *
     * @param byPosition the set each position the reading divided was read to leave, a position whose
     *                   rules leave it everything included
     * @param reach where the walk that read this input saw a name stand somewhere other than the
     *              position of the same name one step down, which is the one place a name and a
     *              position part company
     */
    static AdmittedValues of(Map<TermPath, ValueSet> byPosition, NameReach reach) {
        Map<TermPath, ValueSet> sets = Map.copyOf(byPosition);
        return position -> {
            ValueSet held = sets.get(position);
            return held != null ? new Admitted.Values(held) : whatStandsThere(reach, position);
        };
    }

    /**
     * What a lookup that found no set comes back with, from where the walk saw the name stand.
     *
     * <p>The sorting is {@link NameReach#standingOf}'s and the grain is this type's. A writer
     * choosing where to put a value needs which case each position is under; a search narrowing by
     * sets needs only whether there is a position here at all, and carrying the cases into this
     * answer would be offering a reader the means to work a set out of them — which is the sets of
     * other positions answering for this one.
     *
     * <p>Exhaustive, with no {@code default}. A way for a name to stand somewhere else is a state
     * whose answer here somebody writes, rather than one joining whichever arm a condition left it
     * in.
     */
    private static Admitted whatStandsThere(NameReach reach, TermPath position) {
        return switch (reach.standingOf(position)) {
            // No name crosses here, so the path is a position or it is nothing — and this
            // measurement has no set for it either way.
            case NameReach.Standing.AtThePathItself _ -> new Admitted.NotWorkedOut();
            case NameReach.Standing.UnderTheCases _ -> new Admitted.StandsUnderTheCases();
            // A name that crosses into some cases and stands nowhere under another. What a row
            // written as that case would hold at the name is a position whose rules were never
            // read, so this is the reading falling short and not the language putting the value
            // below.
            case NameReach.Standing.CasesIncomplete _ -> new Admitted.NotWorkedOut();
        };
    }
}
