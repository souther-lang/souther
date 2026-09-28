package souther.runtime;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

import java.math.BigDecimal;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * The witnesses spec §string-decimal-text is held to: {@code String.toDecimal} reads an optional
 * ASCII sign, ASCII digits, and optionally a point followed by ASCII digits, and answers
 * {@code NotANumber} for everything else. A carrier other than the JVM is checked against the same
 * list, so it is written out here rather than derived from any parser.
 *
 * <p>An accepted row is compared with {@code BigDecimal.equals}, which reads the scale as well as
 * the number: the scale of the answer is the number of digits written after the point, and a
 * Souther {@code ==} would not see it (spec §primitives). The refused rows that matter most are the
 * ones {@code BigDecimal(String)} accepts — exponent notation, a point with nothing on one side,
 * and decimal digits outside ASCII.
 */
class DecimalTextIsPlainAsciiNotationTest {

    static Stream<Arguments> accepted() {
        return Stream.of(
                Arguments.of("0", "0"),
                Arguments.of("7", "7"),
                Arguments.of("007", "7"),
                Arguments.of("+007", "7"),
                Arguments.of("-007", "-7"),
                Arguments.of("0.0", "0.0"),
                Arguments.of("0.000", "0.000"),
                Arguments.of("1.0", "1.0"),
                Arguments.of("1.50", "1.50"),
                Arguments.of("001.50", "1.50"),
                Arguments.of("-0.00", "0.00"),
                Arguments.of("+0.00", "0.00"),
                Arguments.of("-12.5", "-12.5"),
                Arguments.of("0123456789.0123456789", "123456789.0123456789"),
                Arguments.of("999999999999999999999999999999999999.000",
                        "999999999999999999999999999999999999.000"));
    }

    static Stream<String> refused() {
        return Stream.of(
                "",
                "+",
                "-",
                ".",
                "+.",
                ".5",
                "5.",
                "+.5",
                "-5.",
                "1..0",
                "1.2.3",
                "+-5",
                "--5",
                "5-",
                "1e3",
                "1E3",
                "1.5e3",
                "1e-3",
                "1_000",
                "1,000",
                "1,5",
                "0x10",
                "/",                            // one below '0'
                ":",                            // one above '9'
                "1./",
                "1.:",
                " 1",
                "1 ",
                "1\n",
                "1. 5",
                "1.0m",
                "１２３",                        // FULLWIDTH DIGIT ONE, TWO, THREE
                "１２３.４５",                   // full-width digits either side of an ASCII point
                "1.５",                          // FULLWIDTH DIGIT FIVE after the point
                "1．5",                          // FULLWIDTH FULL STOP
                "٣.٥",                          // ARABIC-INDIC DIGIT THREE and FIVE
                "＋1",                          // FULLWIDTH PLUS SIGN
                "−1",                           // MINUS SIGN
                "𝟎.5");                         // MATHEMATICAL BOLD DIGIT ZERO, outside the basic plane
    }

    @ParameterizedTest
    @MethodSource("accepted")
    void decimalTextIsThatNumberAtTheScaleWritten(String text, String carrier) {
        assertEquals(new BigDecimal(carrier), Strings.toDecimal(text), "toDecimal(\"%s\")".formatted(text));
    }

    @ParameterizedTest
    @MethodSource("refused")
    void anythingElseIsNotANumber(String text) {
        assertSame(NotANumber.INSTANCE, Strings.toDecimal(text), "toDecimal(\"%s\")".formatted(text));
    }
}
