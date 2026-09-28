package souther.runtime;

/**
 * The failure case of {@code Rational.toWholeNumber}: the exact value is not a whole number, so no
 * {@code Int} is it. A built-in data with no fields; the only value is {@link #INSTANCE}, mirroring
 * {@link NotANumber}.
 *
 * <p>A case rather than a rounded answer. That narrowing is the exact one and states no rounding
 * rule, so where the carrier holds no such value there is nothing for it to hand back — a model that
 * wants a whole number whatever the fraction says by which rule, and asks for it by the operation
 * that takes one.
 */
public final class NotWhole {

    public static final NotWhole INSTANCE = new NotWhole();

    public NotWhole() {}
}
