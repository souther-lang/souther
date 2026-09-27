package souther.runtime;

import java.math.BigDecimal;
import org.jspecify.annotations.Nullable;

/**
 * What a bare value is asked before a decoder reads a scalar from it, where the JVM's carriers say
 * more than the language does (spec {@code [#a-boundary-scalar-is-read-not-converted]}).
 *
 * <p>The language says an {@code Int} is read from an integer representation and a {@code Decimal}
 * from an exact one. Which carriers are those is the binding's to say. A {@code Long}, an
 * {@code Integer}, a {@code Short}, a {@code Byte} and a {@code BigInteger} are integer
 * representations, and a {@code BigDecimal} is when its scale is nought: one with a scale —
 * {@code 5.00}, {@code 5E+2} — is a number written with a fractional form, and reading it as an
 * {@code Int} because its value happens to be whole would be deciding after the fact what the
 * representation meant. A {@code Double} and a {@code Float} are neither: each may have been rounded
 * before it arrived, and what it prints is the shortest text that names the binary value it was
 * rounded to, not the number it was read from.
 *
 * <p>Like the temporal questions in {@code Temporals}, these stop at the fact and answer why a
 * carrier is not one, or null; that a refusal is a failure at a path is the decoder's to say, and
 * the runtime does not know Raoh.
 */
public final class BoundaryScalars {

    /** What is said of a number that may have been rounded before it arrived. */
    public static final String ROUNDED =
            "is a floating-point number and may have been rounded before it arrived";

    private BoundaryScalars() {}

    /** Why a bare value is not an integer representation, or null where it is one or is not a
     *  number carrier this asks about, which the decoder that reads it has its own answer for. */
    public static @Nullable String intRefusal(Object value) {
        return value instanceof BigDecimal number && number.scale() != 0
                ? "is not written as an integer" : null;
    }

    /** Why a bare value is not an exact number, or null where it is one or is not a carrier this
     *  asks about. */
    public static @Nullable String decimalRefusal(Object value) {
        return value instanceof Double || value instanceof Float ? ROUNDED : null;
    }
}
