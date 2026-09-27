package souther.compiler.core;

import souther.compiler.regex.PatternMeaning;

import java.math.BigDecimal;

/**
 * A rule the boundary can state as one of the constraints a decoder names, because the part of a
 * clause it stands for says exactly that of the value of a data made of one field — the value a
 * newtype crosses as.
 *
 * <p>Exactly. A constraint weaker than the part would let through what the clause refuses, and one
 * stronger would refuse at the boundary a value the domain accepts, where it reads as bad input. So
 * each of these is the checker's claim that the part and the constraint admit the same values, made
 * once, and a backend reading one decides nothing about what the rule means — only what its decoder
 * calls the constraint and how it runs it.
 *
 * <p>Which code, message and metadata a failure of each is reported with are not here. They are the
 * decoder library's, and each backend reaches them through its own.
 *
 * <p>Grouped by the type of that field, since a constraint is about a value of one:
 * a {@code String}'s length and format, an {@code Int}'s and a {@code Decimal}'s bounds, a
 * {@code List}'s size and distinctness, a {@code Map}'s size.
 */
public sealed interface BoundaryConstraint {

    /** About a {@code String}. */
    sealed interface OfString extends BoundaryConstraint {}

    /** At least {@code n} characters. */
    record MinLength(int n) implements OfString {}

    /** At most {@code n} characters. */
    record MaxLength(int n) implements OfString {}

    /** Exactly {@code n} characters. */
    record FixedLength(int n) implements OfString {}

    /**
     * The whole string matches a pattern.
     *
     * @param meaning what the pattern matches, as the checker read it — a backend writes it for its
     *     own engine
     * @param written the pattern the author's call was given, which is what a failure says the value
     *     was held to
     */
    record Pattern(PatternMeaning meaning, String written) implements OfString {

        public Pattern {
            if (meaning == null || written == null) {
                throw new IllegalArgumentException(
                        "a pattern is what it matches and what it was written as");
            }
        }
    }

    /** About an {@code Int}. */
    sealed interface OfInt extends BoundaryConstraint {}

    /** At least {@code n}. */
    record Min(long n) implements OfInt {}

    /** At most {@code n}. */
    record Max(long n) implements OfInt {}

    /** Above nought, stated as the bound at nought it was written as rather than a minimum of one. */
    record Positive() implements OfInt {}

    /** Not below nought. */
    record NonNegative() implements OfInt {}

    /** About a {@code Decimal}. */
    sealed interface OfDecimal extends BoundaryConstraint {}

    /** At least {@code n}. */
    record DecimalMin(BigDecimal n) implements OfDecimal {

        public DecimalMin {
            if (n == null) {
                throw new IllegalArgumentException("a bound is a number");
            }
        }
    }

    /** At most {@code n}. */
    record DecimalMax(BigDecimal n) implements OfDecimal {

        public DecimalMax {
            if (n == null) {
                throw new IllegalArgumentException("a bound is a number");
            }
        }
    }

    /** Above nought. */
    record DecimalPositive() implements OfDecimal {}

    /** Not below nought. */
    record DecimalNonNegative() implements OfDecimal {}

    /** About a {@code List}. */
    sealed interface OfList extends BoundaryConstraint {}

    /** At least one element, stated as emptiness rather than as a minimum of one. */
    record NonEmpty() implements OfList {}

    /** At least {@code n} elements. */
    record MinSize(int n) implements OfList {}

    /** At most {@code n} elements. */
    record MaxSize(int n) implements OfList {}

    /** Exactly {@code n} elements. */
    record FixedSize(int n) implements OfList {}

    /** No element appears twice, compared by value as Souther compares. */
    record Unique() implements OfList {}

    /** About a {@code Map}. */
    sealed interface OfMap extends BoundaryConstraint {}

    /** At least {@code n} entries. */
    record MapMinSize(int n) implements OfMap {}

    /** At most {@code n} entries. */
    record MapMaxSize(int n) implements OfMap {}
}
