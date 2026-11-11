package souther.runtime;

import org.jspecify.annotations.Nullable;
import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A narrowing to an {@code Int} refuses a value past the bound of an {@code Int} as the language's
 * refusal, whatever this run has room to build: the bound is asked of the value before the whole
 * number it rounds to is (spec §an-operation-refuses-only-what-its-own-answer-has-no-place-for).
 *
 * <p>Each narrowing is held to an oracle, the whole number {@code BigDecimal} rounds to and whether
 * an {@code Int} holds it, over values near either end of the {@code Int}s and around the number of
 * whole digits a decimal is rounded as written at; a {@code Decimal} and the {@code Rational} of the
 * same value answer alike. Past the end by more than a representation can write, the refusal is
 * still the language's and not a run short of room.
 */
class ANarrowingToAnIntAsksTheBoundOfAnIntBeforeItBuildsAWholeNumberTest {

    private static final List<RoundingMode> MODES = List.of(HALF_UP.INSTANCE, HALF_EVEN.INSTANCE,
            HALF_DOWN.INSTANCE, UP.INSTANCE, DOWN.INSTANCE, CEILING.INSTANCE, FLOOR.INSTANCE);

    private static final BigDecimal LEAST = BigDecimal.valueOf(Long.MIN_VALUE);
    private static final BigDecimal GREATEST = BigDecimal.valueOf(Long.MAX_VALUE);

    /** Values within reach of the oracle: at, inside and past each end by a whole number or less,
     *  and either side of eighteen whole digits. */
    private static final List<BigDecimal> NEAR = List.of(
            LEAST, LEAST.subtract(new BigDecimal("0.5")), LEAST.subtract(new BigDecimal("0.4")),
            LEAST.subtract(new BigDecimal("0.999")), LEAST.subtract(BigDecimal.ONE),
            LEAST.add(new BigDecimal("0.5")),
            GREATEST, GREATEST.add(new BigDecimal("0.5")), GREATEST.add(new BigDecimal("0.4")),
            GREATEST.add(new BigDecimal("0.999")), GREATEST.add(BigDecimal.ONE),
            GREATEST.subtract(new BigDecimal("0.5")),
            new BigDecimal("999999999999999999.5"), new BigDecimal("-999999999999999999.5"),
            new BigDecimal("9999999999999999999.5"), new BigDecimal("-9999999999999999999.5"),
            new BigDecimal("1E+18"), new BigDecimal("1E+19"), new BigDecimal("-1E+19"),
            new BigDecimal("2.5"), new BigDecimal("-2.5"), new BigDecimal("0.0001"));

    /** The oracle: what the value rounds to by {@code mode}, or null where no {@code Int} is it. */
    private static @Nullable Long expected(BigDecimal value, RoundingMode mode) {
        BigDecimal whole = value.setScale(0, DecimalMath.toJava(mode));
        return whole.compareTo(LEAST) < 0 || whole.compareTo(GREATEST) > 0 ? null
                : whole.longValueExact();
    }

    private static void holds(@Nullable Long expected, Supplier<Long> narrowed, String what) {
        if (expected == null) {
            assertThrows(ConstraintViolation.class, narrowed::get, what);
        } else {
            assertEquals(expected, narrowed.get(), what);
        }
    }

    @Test
    void aNarrowingAnswersWhatTheValueRoundsToOrRefusesWhereNoIntIsIt() {
        WorkCheckpoint counted = _ -> { };
        for (BigDecimal value : NEAR) {
            for (RoundingMode mode : MODES) {
                Long expected = expected(value, mode);
                String what = value.toPlainString() + " by " + mode;
                holds(expected, () -> DecimalMath.toInt(mode, value), "Decimal " + what);
                holds(expected, () -> DecimalMath.toInt(mode, value, counted),
                        "Decimal, counted, " + what);
                holds(expected, () -> RationalMath.toInt(mode, Rational.of(value)),
                        "Rational " + what);
                holds(expected, () -> RationalMath.toInt(mode, Rational.of(value), counted),
                        "Rational, counted, " + what);
            }
        }
    }

    /** The exact narrowing holds a whole value to the same bound. */
    @Test
    void aWholeValueIsAnIntExactlyWhereTheBoundHoldsIt() {
        for (BigDecimal value : List.of(LEAST, GREATEST, LEAST.subtract(BigDecimal.ONE),
                GREATEST.add(BigDecimal.ONE))) {
            Long expected = expected(value, DOWN.INSTANCE);
            holds(expected, () -> (Long) RationalMath.toWholeNumber(Rational.of(value)),
                    value.toPlainString());
        }
    }

    /**
     * Ten to the 2147483648 and its negation are past the bound under every mode, and so are ten
     * to a power no exponent of a {@code BigDecimal} reaches: refused as no {@code Int}, and not as
     * a whole number this run has no room to write.
     */
    @Test
    void aValueFarPastTheBoundIsRefusedAsNoIntAndNotAsARunShortOfRoom() {
        BigDecimal far = new BigDecimal(BigInteger.ONE, Integer.MIN_VALUE);
        Rational farther = Rational.of(far).times(Rational.of(far));
        for (RoundingMode mode : MODES) {
            for (BigDecimal value : List.of(far, far.negate())) {
                assertThrows(ConstraintViolation.class, () -> DecimalMath.toInt(mode, value),
                        "Decimal " + value + " by " + mode);
                assertThrows(ConstraintViolation.class,
                        () -> RationalMath.toInt(mode, Rational.of(value)),
                        "Rational " + value + " by " + mode);
            }
            assertThrows(ConstraintViolation.class, () -> RationalMath.toInt(mode, farther),
                    "Rational " + farther + " by " + mode);
            assertThrows(ConstraintViolation.class,
                    () -> RationalMath.toInt(mode, farther.negated()),
                    "Rational -" + farther + " by " + mode);
        }
        assertThrows(ConstraintViolation.class, () -> RationalMath.toWholeNumber(farther));
    }
}
