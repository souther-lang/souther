package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.runtime.DecimalMath;
import souther.runtime.RoundingMode;

import java.math.BigDecimal;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the fold makes of a decimal operation is what the run time computes.
 *
 * <p>A rule folded to true over a value is the reason the value is said to exist, so a fold that
 * rounded or compared differently from the run time would show values to exist that a program
 * refuses. Each operation is folded as a rule of a declaration and asked whether a value of it is
 * shown to exist: the rule states the run time's own answer, so it holds exactly where the fold
 * agrees, and a rule stating any other answer is one nothing is shown of.
 */
class ADecimalFoldsToWhatTheRunTimeComputesTest {

    private static final Map<String, RoundingMode> MODES = Map.of(
            "HALF_UP", souther.runtime.HALF_UP.INSTANCE,
            "HALF_EVEN", souther.runtime.HALF_EVEN.INSTANCE,
            "HALF_DOWN", souther.runtime.HALF_DOWN.INSTANCE,
            "UP", souther.runtime.UP.INSTANCE,
            "DOWN", souther.runtime.DOWN.INSTANCE,
            "CEILING", souther.runtime.CEILING.INSTANCE,
            "FLOOR", souther.runtime.FLOOR.INSTANCE);

    private static final List<String> NUMBERS =
            List.of("0.25m", "0.35m", "-0.25m", "-1.5m", "2.5m", "1.005m", "123.456m", "0.0m");

    private static boolean holdsAValue(String rule) {
        String source = """
                module example.folded

                data Subject = { a: Int, b: Int }
                    invariant only = %s

                data Ok

                behavior take : (n: Subject) -> Ok
                let take (n) = Ok
                """.formatted(rule);
        Compilation compilation = Compilation.ofSource(source, "Main");
        String module = compilation.modules().get(0);
        TypeSymbol subject = TypeSymbols.declared(new TypeKey(module, "Subject"));
        return Rules.of(subject, RuleReadingContext.unshared(RuleReadings.of(compilation, module),
                ReadAs.THE_COMPILATION_DOES, TestDay.TODAY)).bounds().shownToHoldAValue();
    }

    /** A rule needing the product of the two numbers to fold, so no bound speaks for it. */
    private static String about(String decimal, String expected) {
        return "a * b == 0 && Decimal.compare(" + decimal + ", " + expected + ") == 0";
    }

    @Test
    void aRoundingIsWhatTheRunTimeRoundsTo() {
        for (Map.Entry<String, RoundingMode> mode : MODES.entrySet()) {
            for (String number : NUMBERS) {
                for (int scale = 0; scale <= 2; scale++) {
                    BigDecimal written = new BigDecimal(number.substring(0, number.length() - 1));
                    String expected = DecimalMath.round(scale, mode.getValue(), written)
                            .toPlainString() + "m";
                    String rounded = "Decimal.round(" + scale + ", " + mode.getKey() + ", "
                            + number + ")";
                    assertTrue(holdsAValue(about(rounded, expected)),
                            rounded + " is " + expected + " at run time");
                }
            }
        }
    }

    @Test
    void aRoundingTheRunTimeDoesNotAnswerIsNotShown() {
        assertFalse(holdsAValue(about("Decimal.round(1, HALF_UP, 0.25m)", "0.2m")),
                "half up takes 0.25 to 0.3");
        assertEquals(new BigDecimal("0.3"),
                DecimalMath.round(1, souther.runtime.HALF_UP.INSTANCE, new BigDecimal("0.25")));
    }

    @Test
    void aComparisonIsByAmountAndNotByHowADecimalIsWritten() {
        assertTrue(holdsAValue("a * b == 0 && Decimal.compare(1.50m, 1.5m) == 0"));
        assertEquals(0L, DecimalMath.compare(new BigDecimal("1.50"), new BigDecimal("1.5")));
        assertTrue(holdsAValue("a * b == 0 && Decimal.compare(1.5m, 2.5m) == -1"));
        assertEquals(-1L, DecimalMath.compare(new BigDecimal("1.5"), new BigDecimal("2.5")));
    }

    @Test
    void aWholeNumberIsTheDecimalItWritesExactly() {
        assertTrue(holdsAValue(about("Decimal.fromInt(7)", "7.0m")));
        assertEquals(0L, DecimalMath.compare(DecimalMath.fromInt(7), new BigDecimal("7.0")));
    }
}
