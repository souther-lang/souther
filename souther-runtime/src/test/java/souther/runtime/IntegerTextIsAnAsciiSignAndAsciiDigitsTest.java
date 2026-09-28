package souther.runtime;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * The witnesses spec §string-integer-text is held to: {@code String.toInt} reads an optional ASCII
 * sign and ASCII digits, answers {@code NotANumber} for everything else, and answers
 * {@code NotANumber} for a number outside {@code Int} rather than aborting. A carrier other than the
 * JVM is checked against the same list, so it is written out here rather than derived from any
 * parser. The refused rows that matter most are the ones a host number parser accepts — a plus
 * sign's neighbours, and decimal digits outside ASCII, which {@code Long.parseLong} reads through
 * its JDK's Unicode table.
 */
class IntegerTextIsAnAsciiSignAndAsciiDigitsTest {

    static Stream<Arguments> accepted() {
        return Stream.of(
                Arguments.of("0", 0L),
                Arguments.of("7", 7L),
                Arguments.of("42", 42L),
                Arguments.of("0123456789", 123456789L),
                Arguments.of("007", 7L),
                Arguments.of("-007", -7L),
                Arguments.of("+007", 7L),
                Arguments.of("-5", -5L),
                Arguments.of("+5", 5L),
                Arguments.of("-0", 0L),
                Arguments.of("+0", 0L),
                Arguments.of("9223372036854775807", Long.MAX_VALUE),
                Arguments.of("-9223372036854775808", Long.MIN_VALUE),
                Arguments.of("9223372036854775806", Long.MAX_VALUE - 1),
                Arguments.of("-9223372036854775807", Long.MIN_VALUE + 1),
                Arguments.of("0000000000000000000009223372036854775807", Long.MAX_VALUE));
    }

    static Stream<String> refused() {
        return Stream.of(
                "",
                "+",
                "-",
                "+-5",
                "--5",
                "++5",
                "5-",
                "5+",
                "12x",
                "x12",
                "1.0",
                "1e3",
                "1_000",
                "1,000",
                "0x10",
                "/",                            // one below '0'
                ":",                            // one above '9'
                " 5",
                "5 ",
                "5\n",
                "　5",                          // IDEOGRAPHIC SPACE before the digit
                "- 5",
                "１２３",                        // FULLWIDTH DIGIT ONE, TWO, THREE
                "-５",                          // a sign then FULLWIDTH DIGIT FIVE
                "＋5",                          // FULLWIDTH PLUS SIGN
                "−5",                           // MINUS SIGN
                "٣",                            // ARABIC-INDIC DIGIT THREE
                "१",                            // DEVANAGARI DIGIT ONE
                "𝟎",                            // MATHEMATICAL BOLD DIGIT ZERO, outside the basic plane
                "9223372036854775808",          // one above the largest Int
                "-9223372036854775809",         // one below the smallest Int
                "99999999999999999999");
    }

    @ParameterizedTest
    @MethodSource("accepted")
    void integerTextWithinIntIsThatInteger(String text, long value) {
        assertEquals(value, Strings.toInt(text), "toInt(\"%s\")".formatted(text));
    }

    @ParameterizedTest
    @MethodSource("refused")
    void anythingElseIsNotANumber(String text) {
        assertSame(NotANumber.INSTANCE, Strings.toInt(text), "toInt(\"%s\")".formatted(text));
    }
}
