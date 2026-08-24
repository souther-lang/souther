package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Place;
import souther.compiler.types.TypeSymbol;
import souther.compiler.values.Value;

import java.util.List;

/**
 * What a class is, said as a value rather than as a way of asking.
 *
 * <p>The same fact {@link Classifier} answers with, written down instead of executed. A class means
 * something about the model — this is the {@code true} of a {@code Bool}, this is the {@code Some}
 * of an optional, this is where a count sits against a line the rules drew — and reading a row to
 * find out whether it is in one is what a tool does about that meaning. Held as a function, the
 * meaning existed only while something was calling it: the class could not be compared with another
 * class, could not be kept in an answer, and had to be built again by every reader that wanted one.
 *
 * <p><b>Why that mattered.</b> An answer this compiler keeps has to compare as a value, because an
 * edit is absorbed by an answer coming out equal to the one it replaces ({@code Key}). A class
 * carrying a lambda compares by identity, so the partitioning it belongs to could never be an answer
 * — and it was not one: three separate readers worked out the same partitioning for themselves from
 * the declarations, which is one meaning derived in three places (issue #1001).
 *
 * <p>Every arm here was a lambda written at one place in this package. Which arms there are is
 * therefore a closed question about what this compiler distinguishes today, and a distinction added
 * later arrives as an arm rather than as a function nobody can look inside.
 *
 * @see Recognitions the one place that reads one of these against a value
 */
public sealed interface Recognition {

    /** One of the two values of a {@code Bool}. */
    record Truth(boolean value) implements Recognition {}

    /** Whether an optional holds anything, which is the one division its type makes. */
    record Held(boolean present) implements Recognition {}

    /** One case of a sum, told by the construction the row wrote. */
    record OfCase(TypeSymbol leaf) implements Recognition {}

    /** The one value a reading singled out, told by reading the value itself. */
    record AtAValue(Value value) implements Recognition {}

    /**
     * Where a count sits, read out of the row through the carrier that says how its values step.
     *
     * <p>One arm for the three ways a count is asked about, because reading the count is the part
     * they share and it is the part that can fail. Written as three arms, the walk from the row to
     * the number — and what a value that is not a number, or one that could not be read, comes to —
     * was spelled twice in this package and would have been spelled a third time by the next one.
     */
    record OfACount(NumericTerm term, Carrier carrier, CountIs is) implements Recognition {}

    /** What is asked of the count once it has been read. */
    sealed interface CountIs {

        /** Exactly the value a rule singled out. */
        record At(Place value) implements CountIs {}

        /** None of the values any rule singled out, which is the class those leave behind. */
        record AwayFrom(List<Place> values) implements CountIs {

            public AwayFrom {
                values = List.copyOf(values);
            }
        }

        /** Inside one of the runs the lines a rule drew cut the position into. */
        record InARun(Band run) implements CountIs {}
    }

    /**
     * The same class, asked of the value inside the names the position writes it under.
     *
     * <p>The other direction of the same fact a representative is written by: a position declaring
     * {@code data StageN = Stage} divides into the cases of {@code Stage}, and a row writes
     * {@code StageN(Prospecting)}.
     *
     * @param worn the names, outermost first, as {@code TypeView} reads them off the position
     */
    record Under(List<TypeSymbol> worn, Recognition inner) implements Recognition {

        public Under {
            worn = List.copyOf(worn);
            if (worn.isEmpty()) {
                // Nothing is worn, so this says the same thing as what it wraps while comparing
                // unequal to it. Two ways of writing one class is what a value is for stopping.
                throw new IllegalArgumentException(
                        "a class under no names at all: " + inner + ". Use the inner class itself");
            }
        }

        /** {@code inner} under {@code worn}, or {@code inner} itself where nothing is worn. */
        public static Recognition of(List<TypeSymbol> worn, Recognition inner) {
            return worn.isEmpty() ? inner : new Under(worn, inner);
        }
    }

    /** A class that exists and cannot be told from another by looking. */
    record Nothing() implements Recognition {}
}
