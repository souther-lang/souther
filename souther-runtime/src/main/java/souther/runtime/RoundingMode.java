package souther.runtime;

import java.util.Comparator;

/**
 * The rounding-mode enumeration core declares as {@code data RoundingMode} (spec 18.3). The
 * declaration lives in {@code souther/decimal.sou}; the implementation is provided here rather than
 * generated, like {@link Option} and {@link DivisionByZero}, so the static shape mirrors what the
 * compiler emits for a unit-only sum: a sealed interface carrying {@code __tag}, {@code __order}
 * and {@code __ordering}, and one record per case holding its {@code INSTANCE}.
 */
public sealed interface RoundingMode
        permits HALF_UP, HALF_EVEN, HALF_DOWN, UP, DOWN, CEILING, FLOOR {

    /** Which case a value of this enumeration is. */
    static String __tag(Object v) {
        return switch (v) {
            case HALF_UP _ -> "HALF_UP";
            case HALF_EVEN _ -> "HALF_EVEN";
            case HALF_DOWN _ -> "HALF_DOWN";
            case UP _ -> "UP";
            case DOWN _ -> "DOWN";
            case CEILING _ -> "CEILING";
            case FLOOR _ -> "FLOOR";
            default -> throw new IllegalStateException();
        };
    }

    /** Where a value's case stands in the declaration. */
    static int __order(Object v) {
        return switch (v) {
            case HALF_UP _ -> 0;
            case HALF_EVEN _ -> 1;
            case HALF_DOWN _ -> 2;
            case UP _ -> 3;
            case DOWN _ -> 4;
            case CEILING _ -> 5;
            case FLOOR _ -> 6;
            default -> throw new IllegalStateException();
        };
    }

    static Comparator<Object> __ordering() {
        return Comparator.comparingInt(RoundingMode::__order);
    }
}
