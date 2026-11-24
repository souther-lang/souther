package souther.compiler.values;

import souther.compiler.observe.ObservedValue;

import java.math.BigDecimal;

/**
 * What an observation denotes as a {@link Value}: the one place a run's leftovers are read back as
 * what a rule names.
 *
 * <p>Here and not on {@link ObservedValue} because the values of this package already depend on the
 * observations, and an observation answering a question about a {@code Value} would make the two
 * depend on each other. Every reader that asks which observations are which written value asks it
 * here, so two numerals of one number are one value for all of them.
 */
public final class WrittenValues {

    private WrittenValues() {}

    /**
     * The value {@code seen} is an observation of, or null where no value is written for it.
     *
     * <p>Null is "no value is written for this" and not "it is unlike everything". A moment, a
     * sequence and a mapping are observations of positions whose values are told apart another way,
     * a construction is told apart by which declaration it is and not by a value, and an observation
     * that stopped short has no value yet.
     *
     * <p>A number comes back as the number and not as the writing of it, which {@link Value.Number}
     * holds: {@code 1} read as an {@code Int} and {@code 1.00} read as a {@code Decimal} are one
     * value.
     */
    public static Value denotedBy(ObservedValue seen) {
        return switch (seen) {
            case ObservedValue.Text it -> Value.text(it.value());
            case ObservedValue.Bool it -> Value.truth(it.value());
            case ObservedValue.Integer it -> Value.number(BigDecimal.valueOf(it.value()));
            case ObservedValue.Decimal it -> Value.number(it.value());
            case ObservedValue.Unit it -> Value.of(it.type());
            case ObservedValue.Temporal _, ObservedValue.Constructed _, ObservedValue.Sequence _,
                 ObservedValue.Mapping _, ObservedValue.Absent _, ObservedValue.Unknown _,
                 ObservedValue.Truncated _ -> null;
        };
    }

    /**
     * Whether {@code seen} is an observation of {@code written}, or null where the two are of kinds
     * no row writes alike.
     *
     * <p>Null is the third answer and is kept apart from false: a text against a number is not an
     * unequal pair of values but a pair no row compares, and a denial of the comparison must not
     * hold there.
     *
     * <p>A scalar written is the value a position holds under whatever newtypes it wears, so it is
     * compared with what the row holds inside them. A case is the construction or unit itself.
     */
    public static Boolean denotes(ObservedValue seen, Value written) {
        ObservedValue bare = written instanceof Value.Case ? seen : ObservedValue.scalarInside(seen);
        Value actual = denotedBy(bare);
        if (actual == null || actual.getClass() != written.getClass()) {
            return null;
        }
        return written.equals(actual);
    }
}
