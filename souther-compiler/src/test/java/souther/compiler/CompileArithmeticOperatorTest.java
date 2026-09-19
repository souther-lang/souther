package souther.compiler;

import souther.compiler.diag.CompileException;

import souther.runtime.ConstraintViolation;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The arithmetic operators {@code + - * /} over Int and Decimal (spec
 * §an-operator-takes-the-types-it-is-defined-for). A Decimal literal carries the {@code m} suffix (F# form).
 * {@code /} aborts on a zero divisor (like overflow), while {@code Int.truncatingDivide} and
 * {@code Decimal.divide} return {@code X | DivisionByZero} for case handling. Over either pair of
 * numbers {@code /} answers an exact quotient, so a number of the operand's own type is narrowed at
 * the point the model wants one (spec §stdlib-rational).
 */
class CompileArithmeticOperatorTest {

    private Object run(String module, String behavior, String type, Object input) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(module), getClass().getClassLoader());
        Object in = Codecs.decoded(loader, "demo." + type, input);
        Object b = Emitted.behavior(loader, "demo", behavior).getDeclaredConstructor().newInstance();
        Object out = Codecs.apply(b, in);
        return Codecs.encode(loader, "demo." + type, out);
    }

    private static final String INT_CALC = """
            module demo
            data N = Int
            behavior calc : (n: N) -> N constructs N
            let calc (n) = N { value = %s }
            """;

    private static final String DEC_CALC = """
            module demo
            data Money = Decimal
            behavior calc : (m: Money) -> Money constructs Money
            let calc (m) = Money { value = %s }
            """;

    @Test
    void intOperators() throws Exception {
        assertEquals(14L, run(INT_CALC.formatted("n.value * 3 - 1"), "calc", "N", 5L));
        // `/` is exact, so the whole-number answer is the one a rounding mode makes of it
        assertEquals(3L, run(INT_CALC.formatted("Rational.toInt(DOWN, n.value / 2)"), "calc", "N", 7L));
        assertEquals(4L,
                run(INT_CALC.formatted("Rational.toInt(HALF_UP, n.value / 2)"), "calc", "N", 7L));
    }

    @Test
    void decimalOperators() throws Exception {
        // 5 + 10.5 = 15.5, via the `+` operator and the `10.5m` literal
        assertEquals(new BigDecimal("15.5"),
                run(DEC_CALC.formatted("m.value + 10.5m"), "calc", "Money", new BigDecimal("5")));
        // an integer-valued Decimal literal carries `m` too
        assertEquals(0, ((BigDecimal) run(DEC_CALC.formatted("500m"), "calc", "Money", new BigDecimal("1")))
                .compareTo(new BigDecimal("500")));
    }

    /** The quotient of two Decimals, which the operator answers exactly (spec §stdlib-rational). */
    private static final String DEC_QUOTIENT = """
            module demo
            data Money = Decimal
            behavior calc : (m: Money) -> Money constructs Money
            let calc (m) =
                match %s with
                    | Decimal as d -> Money { value = d }
                    | NotAFiniteDecimal -> Money { value = 0m }
            """;

    /** The same quotient asked whether it is a whole number, which a third multiplied back is. */
    private static final String DEC_WHOLE = """
            module demo
            data Money = Decimal
            behavior calc : (m: Money) -> Money constructs Money
            let calc (m) =
                match %s with
                    | Int as n -> Money { value = Decimal.fromInt(n) }
                    | NotWhole -> Money { value = 0m }
            """;

    @Test
    void decimalDivisionIsExact() throws Exception {
        // Ten over four is a decimal, and comes back as the decimal it is.
        assertEquals(new BigDecimal("2.5"),
                run(DEC_QUOTIENT.formatted("Rational.toFiniteDecimal(m.value / 4m)"),
                        "calc", "Money", new BigDecimal("10")));
        // A third is no decimal at all, which is the answer a quotient rounded to a precision
        // nobody chose could not give: that one is a Decimal, and a terminating one.
        assertEquals(new BigDecimal("0"),
                run(DEC_QUOTIENT.formatted("Rational.toFiniteDecimal(m.value / 3m)"),
                        "calc", "Money", new BigDecimal("10")));
        // And the whole of the division is kept: multiplied back by the divisor it is the
        // dividend, where a rounded quotient answers a number with a fraction on the end of it.
        assertEquals(new BigDecimal("10"),
                run(DEC_WHOLE.formatted("Rational.toWholeNumber(m.value / 3m * 3m)"),
                        "calc", "Money", new BigDecimal("10")));
    }

    @Test
    void divisionByZeroAborts() {
        // the `/` operator aborts (like overflow); `Int.truncatingDivide` is the case-returning form
        assertThrows(ConstraintViolation.class,
                () -> run(INT_CALC.formatted("Rational.toInt(DOWN, n.value / 0)"), "calc", "N", 5L));
        assertThrows(ConstraintViolation.class,
                () -> run(DEC_CALC.formatted("Rational.toDecimal(2, HALF_UP, m.value / 0m)"),
                        "calc", "Money", new BigDecimal("5")));
    }

    @Test
    void aFractionalLiteralWithoutMIsRejected() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compile(DEC_CALC.formatted("1.5")));
        assertTrue(e.getMessage().contains("m"), "the diagnostic should point at the `m` suffix: " + e.getMessage());
    }
}
