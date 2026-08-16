package souther.compiler.values;

import souther.compiler.types.TypeSymbol;

import java.math.BigDecimal;

/**
 * One value a model can write out, as the thing it denotes rather than as the text it was written
 * with.
 *
 * <p>What this is for is deciding whether two rules name the same value. {@code == "A"} beside
 * {@code == "B"} admits nothing and {@code == "A"} beside {@code == "A"} admits one thing, and the
 * whole of the difference is an equality between two of these.
 *
 * <p>Sealed, so a kind of value added to the language is a build failure at every reader rather
 * than a literal quietly answering that it is unlike everything including itself.
 *
 * <p>What is not here is as much of the design as what is. A date, a time and an instant are
 * ordered and each has a count that stands for it, so what two of them admit together is a question
 * the interval algebra answers over that count; putting them here as well would give one position
 * two ways of being told which values it has, and the two would have to be kept agreeing. The line
 * is not that a date is unlike a string — it is that a date already has a domain and a string has
 * none.
 */
public sealed interface Value {

    /** A string, standing for itself. */
    record Text(String value) implements Value {

        public Text {
            if (value == null) {
                throw new IllegalArgumentException("a written string is not absent");
            }
        }
    }

    /**
     * A number, kept in the one form that makes two writings of it one value.
     *
     * <p>{@code 1.0m} and {@code 1.00m} are the same value where they are written, and the interval
     * algebra already reads them as one: a declaration bounded at both by equality is admitted,
     * where the same declaration bounded at {@code 1.0m} and {@code 2.0m} is refused. Two domains
     * disagreeing about which numbers are the same number would leave one position with two sets of
     * values it may hold, so this holds the same identity that one does. Nothing here decides what
     * the language compares equal; it follows what the reading beside it already does.
     *
     * <p>An {@code Int} and a {@code Decimal} cannot be compared with each other, so a position is
     * written about in one of them and never in both.
     */
    record Number(BigDecimal value) implements Value {

        public Number {
            if (value == null) {
                throw new IllegalArgumentException("a written number is not absent");
            }
            value = value.stripTrailingZeros();
        }
    }

    /** A boolean. */
    record Truth(boolean value) implements Value {}

    /**
     * One case of an enumeration, named by the declaration it is.
     *
     * <p>A case holds nothing, so what tells two of them apart is which declaration each is, which
     * is what a name is for. Read the same way wherever an enumeration is written out.
     */
    record Case(TypeSymbol data) implements Value {

        public Case {
            if (data == null) {
                throw new IllegalArgumentException("a case is named by a declaration");
            }
        }
    }

    static Value text(String value) {
        return new Text(value);
    }

    static Value number(BigDecimal value) {
        return new Number(value);
    }

    static Value number(long value) {
        return new Number(BigDecimal.valueOf(value));
    }

    static Value truth(boolean value) {
        return new Truth(value);
    }

    static Value of(TypeSymbol data) {
        return new Case(data);
    }
}
