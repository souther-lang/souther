package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Place;
import souther.compiler.types.TypeSymbol;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;

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
 * the declarations, which is one meaning derived in three places.
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
    record OfCase(TypeSymbol leaf, Place at) implements Recognition {}

    /**
     * The one value a reading singled out, told by reading the value itself.
     *
     * @param value what the class holds, which is what a row is read against
     * @param at    where that value sits on the order of what stands at the position, or null where
     *              nothing places it there. The one crossing between the two ways a class is asked
     *              about, made where the position's type and the value are both in hand: a reader
     *              holding a place on that order has no value to read, and one that placed the value
     *              itself would be placing it on whatever order it had reached for. Null is "nothing
     *              placed it" and never "it is nowhere" — a position with no order has no places to
     *              be asked about at all
     */
    record AtAValue(Value value, Place at) implements Recognition {}

    /**
     * Where a count sits, read out of the row through the carrier that says how its values step.
     *
     * <p>One arm for the three ways a count is asked about, because reading the count is the part
     * they share and it is the part that can fail. Written as three arms, the walk from the row to
     * the number — and what a value that is not a number, or one that could not be read, comes to —
     * was spelled twice in this package and would have been spelled a third time by the next one.
     */
    record OfACount(NumericTerm.FromOnePosition term,
                    souther.compiler.inputs.TermOrders orders, CountIs is)
            implements Recognition {

        public OfACount {
            // The term is here because a class of one position's count is asked about a position,
            // which is the narrower of the two kinds of term; the orders say which number they are
            // of. Two spellings of one thing, so the second is refused here rather than read as a
            // class of a number the row is not asked about.
            orders.areOf(term);
        }

        /** What the count is compared on, which is what the class was written in. */
        public Carrier carrier() {
            return orders.answered();
        }
    }

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

    /**
     * The values a rule told apart from the rest, as the set of them.
     *
     * <p>The first arm that is a set rather than a place. Every other class about what stands at the
     * position is one value, one case, or somewhere on an order — and a rule a behavior writes about
     * a string need be none of those: {@code String.startsWith("JP", code)} admits strings without
     * end and leaves out strings without end, and the two are what the behavior treats differently.
     * Written as a place it would have to be a run, which the strings a pattern admits are not; left
     * out, the position comes back divided nowhere by a body that plainly divides it.
     *
     * <p><b>Both sides are one of these.</b> What a rule admits and what it leaves are two classes
     * of the position, and each is a set — so the far side is the set of the values on it, and never
     * this class under a denial. A class that meant "not that one" would be a second way of saying
     * what a set already says, and two of them could not be met with anything.
     *
     * <p>And the one arm that is asked about a value rather than about a place. The strings a
     * behavior tells apart need not be an interval of the order they are written on, so there is no
     * place a line could fall in this and it says so ({@link #answersAboutAPlace}).
     */
    record OfASet(ValueSet values) implements Recognition {

        public OfASet {
            if (values == null) {
                throw new IllegalArgumentException("a class of a set of values holds a set");
            }
            // A class holds something, and a class of the empty set holds nothing: it is not a
            // class of the position at all, and among the classes of a measure it would be one a
            // report counts, tells an author no row is in, and asks the generator for. What
            // composes these leaves the cells that hold nothing out; one arriving here is that
            // reader having passed one on, and it is refused where the value is made.
            if (values.isEmpty()) {
                throw new IllegalArgumentException(
                        "a class holding no value is not a class of the position");
            }
        }
    }

    /** A class that exists and cannot be told from another by looking. */
    record Nothing() implements Recognition {}

    /**
     * Whether this can be asked about a place on the order the position's values are counted on.
     *
     * <p>Two things a "no" from such a question could mean — the place is not in the class, or the
     * class has no way of being asked — and only the first is an answer. This is the second said on
     * its own, so that an axis carrying lines can refuse a class that could never hold one of them
     * rather than let every line fall in no class at all. A class about a count is asked on that
     * count's order; a case of an ordered enumeration and a value the rules named are asked at the
     * place written down when the class was built; a truth, an absence and a class nothing tells
     * apart are on no order.
     */
    default boolean answersAboutAPlace() {
        return switch (this) {
            case OfACount ignored -> true;
            case Under under -> under.inner().answersAboutAPlace();
            case OfCase one -> one.at() != null;
            case AtAValue one -> one.at() != null;
            case Truth ignored -> false;
            case Held ignored -> false;
            // A set of values is not a run of them, so no place is inside it or outside it in the
            // way a line asks about. Answered yes, a line would fall in whichever of these
            // happened to hold the one value the place stands for, which is an answer about a
            // value where the question was about an order.
            case OfASet ignored -> false;
            case Nothing ignored -> false;
        };
    }

    /**
     * Whether a class meaning this can be a class of {@code number}.
     *
     * <p>Not which measure a class of this divides — that is said where the class is built and is
     * never read off a meaning, because a truth means the same thing at every position. What this
     * answers is whether the two are in one vocabulary. A meaning about a count carries the number
     * it counts, and is a class of that number and of no other. Every other meaning is about the
     * value standing at the position — a case, a truth, a value the rules named, and the place any
     * of them was given is on the order that value is written on — so it is a class of the
     * position's own value and of nothing taken of it. Said to be of a number taken of the
     * position, such a class would hold a place on one order and be asked about places on another,
     * which a {@code Place} on its own cannot tell apart.
     *
     * <p>Exhaustive with no {@code default}: a meaning added later says which vocabulary it is in.
     */
    default boolean canBeAClassOf(NumericTerm.FromOnePosition number) {
        return switch (this) {
            case OfACount count -> count.term().equals(number);
            case Under under -> under.inner().canBeAClassOf(number);
            case Truth ignored -> number instanceof NumericTerm.ValueOf;
            case Held ignored -> number instanceof NumericTerm.ValueOf;
            case OfCase ignored -> number instanceof NumericTerm.ValueOf;
            case AtAValue ignored -> number instanceof NumericTerm.ValueOf;
            // The values are the position's own, which is what the sets a rule about them names
            // hold. A count taken of the position is a number, and a set of the position's values
            // said to be a class of it would answer membership by reading a value of one where the
            // other was owed.
            case OfASet ignored -> number instanceof NumericTerm.ValueOf;
            case Nothing ignored -> number instanceof NumericTerm.ValueOf;
        };
    }
}
