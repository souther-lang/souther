package souther.compiler.coverage;

import souther.compiler.types.TypeSymbol;

import java.math.BigDecimal;
import java.util.Objects;

/**
 * A value a body writes out on one side of a comparison: what the comparison tells apart.
 *
 * <p>A step of a walk that compares an element with {@code 1000} answers differently for an
 * element on either side of it, and no row need hold a number near it for the step to do so. The
 * values a body names are where a row has to be taken to to see what a comparison does, as the
 * values a row holds are where the rows written saw something.
 */
public sealed interface NamedValue {

    /** A whole number the body names. */
    record Whole(long value) implements NamedValue {}

    /** A decimal the body names. */
    record Fractional(BigDecimal value) implements NamedValue {

        public Fractional {
            Objects.requireNonNull(value, "a decimal named is some decimal");
        }
    }

    /** A string the body names. */
    record Characters(String value) implements NamedValue {

        public Characters {
            Objects.requireNonNull(value, "a string named is some string");
        }
    }

    /** A case of a sum the body tells from the others, as an arm of a {@code match} does. */
    record Case(TypeSymbol type) implements NamedValue {

        public Case {
            Objects.requireNonNull(type, "a case named is some case");
        }
    }
}
