package souther.runtime;

/**
 * The failure case of {@code Rational.toFiniteDecimal}: the exact value has no finite decimal, a
 * third being the smallest example. A built-in data with no fields; the only value is
 * {@link #INSTANCE}, mirroring {@link NotWhole}.
 *
 * <p>Which values these are is decided by the value and not by how many digits a caller would accept:
 * a decimal is a whole number over a power of ten, so a fraction whose denominator holds anything ten
 * is not made of repeats however far it is written. A model that wants a decimal at a scale of its own
 * says so, and rounds by a rule it names.
 */
public final class NotAFiniteDecimal {

    public static final NotAFiniteDecimal INSTANCE = new NotAFiniteDecimal();

    public NotAFiniteDecimal() {}
}
