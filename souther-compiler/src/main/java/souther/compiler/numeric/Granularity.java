package souther.compiler.numeric;

/**
 * How the values of one atom are spaced.
 *
 * <p>Not a property of the arithmetic — a {@link NumericDomain.LinearForm} is the same expression
 * whatever its atoms are made of — but of the atom itself, which is why it is registered against the
 * key rather than carried in the form. What it decides is whether a strict bound has a next value to
 * step to: {@code a < b} over whole numbers is {@code a <= b - 1}, and over decimals it is nothing
 * tighter than {@code a <= b}.
 */
public enum Granularity {

    /** Whole numbers, one apart. Souther's {@code Int} and every size. */
    DISCRETE,

    /** No smallest step. Souther's {@code Decimal}. */
    DENSE
}
