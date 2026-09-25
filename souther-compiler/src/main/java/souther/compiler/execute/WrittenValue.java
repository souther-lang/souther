package souther.compiler.execute;

import souther.compiler.partition.FixtureTemplate;

import java.math.BigDecimal;

/**
 * A constant as a Souther source can write one.
 *
 * <p>The four the language has, rather than the object a fold happened to leave behind. What the
 * compiler carries internally is an {@code Object} — a {@code Long}, a {@code Boolean}, a
 * {@code String} or a {@code BigDecimal}, told apart by asking the value what class it is — and a
 * boundary that took one would be handing the machine's answer to that question across as the
 * language's. An implementation that is not the JVM has no reason to know that a whole number
 * arrives as {@code java.lang.Long}.
 *
 * <p>Which primitive each becomes is the implementation's own business and is decided there.
 */
public sealed interface WrittenValue {

    /** The constant as a source writes it: a text quoted and escaped, a decimal at its scale. */
    default String written() {
        return switch (this) {
            case Text(String text) -> FixtureTemplate.quoted(text);
            case Whole(long whole) -> String.valueOf(whole);
            case Truth(boolean truth) -> String.valueOf(truth);
            case Decimal(BigDecimal decimal) -> decimal.toPlainString();
        };
    }

    /** A whole number. */
    record Whole(long value) implements WrittenValue {}

    /** A decimal, at the scale it was written to. */
    record Decimal(BigDecimal value) implements WrittenValue {

        public Decimal {
            if (value == null) {
                throw new IllegalArgumentException("a decimal constant has a value");
            }
        }
    }

    /** Text. */
    record Text(String value) implements WrittenValue {

        public Text {
            if (value == null) {
                throw new IllegalArgumentException("a text constant has a value");
            }
        }
    }

    /** True or false. */
    record Truth(boolean value) implements WrittenValue {}
}
