package souther.compiler.inputs;

import souther.compiler.types.TypeSymbol;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;


/**
 * One distinction a position's declarations state between the values that can stand there.
 *
 * <p>The unit the rules are crossed with, and the unit every measure counts in. What a sum's cases
 * are, what a {@code Bool}'s two values are, whether an optional holds anything and which values a
 * rule singled out are four spellings of the same kind of statement — the model saying that these
 * values are told apart here — and a reading that spoke for only one of them would leave the others
 * to be crossed with the rules somewhere else, which is where two readings of one position start
 * disagreeing.
 *
 * <p>Nothing here is about how a value of the distinction is written down or recognised in a row.
 * That is the partition's work, and it needs a name, a classifier and a recipe; this needs only
 * enough to be held against a rule. So the two questions below are the whole of the interface, and
 * a reader wanting the third asks the partition.
 */
public sealed interface Case {

    /**
     * Whether {@code value} is one this distinction holds.
     *
     * <p>Asked of the distinction, because knowing what it holds is what settles it. The
     * alternative — matching a value against what a class is called — is a second copy of how a
     * class is named.
     */
    boolean holds(Value value);

    /**
     * The values this holds, where they can be written out, and null where they cannot.
     *
     * <p>Null is "not written out here" and never "holds nothing". A case of an enumeration is one
     * value and says so; a case holding a record has no end of values and says nothing, which is
     * what leaves a rule written as a denial unable to prove it empty.
     */
    ValueSet denotes();

    /**
     * Whether {@code admitted} leaves this distinction a value, where that can be settled.
     *
     * <p>One question and two proofs. {@code admitted} is an upper bound on what the position
     * holds, so a distinction holding none of a finite set holds nothing at all; and a set written
     * as a denial proves one empty only by excluding every value it has, which takes knowing what
     * those are. Where neither proof is available the distinction stays: nothing has shown the
     * position cannot reach it, and taking one away on less than that is a distinction the model
     * states going missing.
     */
    default boolean leftAnythingBy(ValueSet admitted) {
        ValueSet held = denotes();
        if (held != null) {
            return !held.meet(admitted).isEmpty();
        }
        return !(admitted instanceof ValueSet.Finite finite)
                || finite.values().stream().anyMatch(this::holds);
    }

    /**
     * One case of a sum, folded to a leaf.
     *
     * @param oneValue whether the case is the whole of a value — a unit data is, and a case holding
     *                 a record or wrapping a value is not. Read off the declaration where the case
     *                 is made rather than asked again here, so that what a case holds and what the
     *                 rules leave it are crossed against one answer
     */
    record SumCase(TypeSymbol leaf, boolean oneValue) implements Case {

        @Override
        public boolean holds(Value value) {
            return value instanceof Value.Case one && leaf.equals(one.data());
        }

        @Override
        public ValueSet denotes() {
            return oneValue ? ValueSet.just(Value.of(leaf)) : null;
        }
    }

    /** One of the two values a {@code Bool} has, which is the whole of what its type divides into. */
    record Truth(boolean value) implements Case {

        @Override
        public boolean holds(Value against) {
            return against instanceof Value.Truth truth && truth.value() == value;
        }

        @Override
        public ValueSet denotes() {
            return ValueSet.just(Value.truth(value));
        }
    }

    /**
     * Whether an optional holds anything, which is the one division its type makes.
     *
     * <p>Holds no value of the rules' language either way: absence is not something a rule here
     * writes down, so {@code Some} holds every value written and {@code None} holds none of them.
     * That is what the reading says today, and saying it here rather than through a shape test on
     * an observation is the same answer with the round trip taken out.
     */
    record Presence(boolean present) implements Case {

        @Override
        public boolean holds(Value value) {
            return present;
        }

        @Override
        public ValueSet denotes() {
            return null;
        }

        /**
         * Neither answer is refused by a set of values.
         *
         * <p>A rule names values, and absence is not one of them: nothing the reading can write
         * down says whether an optional holds something. Left to the rule above, {@code None} is
         * dropped by any finite set for holding none of its values — which is true of every value
         * and says nothing about absence, and now that a refusal takes an arm out of what the rows
         * are owed, that is a row nobody is asked for on the strength of a set that was never about
         * this.
         */
        @Override
        public boolean leftAnythingBy(ValueSet admitted) {
            return true;
        }
    }

    /**
     * One value a rule named, where the position's type states no division of its own.
     *
     * <p>{@code data Gender = String invariant value == "A" || value == "B"} divides its position
     * exactly as {@code data Gender = A | B} does, and this is that division read off the rule.
     */
    record Named(Value value) implements Case {

        @Override
        public boolean holds(Value against) {
            return switch (value) {
                case Value.Text text ->
                        against instanceof Value.Text it && it.value().equals(text.value());
                case Value.Truth truth ->
                        against instanceof Value.Truth it && it.value() == truth.value();
                // Compared as numbers and not as writings of them. `1.0m` and `1.00m` are one
                // value where they are written, and the reading that named this is holding them
                // as one already.
                case Value.Number number -> against instanceof Value.Number it
                        && it.value().compareTo(number.value()) == 0;
                case Value.Case one ->
                        against instanceof Value.Case it && it.data().equals(one.data());
            };
        }

        @Override
        public ValueSet denotes() {
            return ValueSet.just(value);
        }
    }
}
