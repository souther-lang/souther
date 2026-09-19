package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.runtime.Rational;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What {@code /} answers, and what a model writes to get back out of it (ADR-0116).
 *
 * <p>Every claim here is about the language rather than about the value that carries the quotient:
 * which type the operator answers, which pairs the exact arithmetic admits, which positions refuse
 * one, and what a row a behavior answers with is written from. The arithmetic itself is held where the
 * value is.
 */
class AQuotientIsExactAndLeavesTheOperandTypeTest {

    private static final String INT_CALC = """
            module demo
            data N = Int
            behavior calc : (n: N) -> N constructs N
            let calc (n) = N { value = %s }
            """;

    private Object run(String module, Object input) throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(module), getClass().getClassLoader());
        Object in = Codecs.decoded(loader, "demo.N", input);
        Object b = Emitted.behavior(loader, "demo", "calc").getDeclaredConstructor().newInstance();
        return Codecs.encode(loader, "demo.N", Codecs.apply(b, in));
    }

    private static CompileException refused(String module) {
        return assertThrows(CompileException.class, () -> Compiler.compile(module));
    }

    /** The quotient leaves the operand type, so the field that held the operands does not hold it. */
    @Test
    void aQuotientOfWholeNumbersIsNoWholeNumber() {
        CompileException e = refused(INT_CALC.formatted("n.value / 2"));
        assertTrue(e.getMessage().contains("Rational"), e.getMessage());
    }

    /** And a model says how the fraction becomes one. The rounding is the model's word, which is the
     *  whole point of the operator stating none. */
    @Test
    void aModelSaysHowTheFractionBecomesAWholeNumber() throws Exception {
        assertEquals(3L, run(INT_CALC.formatted("Rational.toInt(DOWN, n.value / 2)"), 7L));
        assertEquals(4L, run(INT_CALC.formatted("Rational.toInt(HALF_UP, n.value / 2)"), 7L));
        assertEquals(4L, run(INT_CALC.formatted("Rational.toInt(CEILING, n.value / 2)"), 7L));
    }

    /** Or asks for the exact one, which answers a case rather than a rounding nobody chose. */
    @Test
    void anExactNarrowingAnswersACaseWhereThereIsNoSuchValue() throws Exception {
        String model = INT_CALC.formatted("""
                match Rational.toWholeNumber(n.value / 2) with
                    | Int as q -> q
                    | NotWhole -> 0 - 1""");
        assertEquals(2L, run(model, 4L));
        assertEquals(-1L, run(model, 7L));
    }

    /** An operand already exact makes the operation exact, and the other side is read at its value. */
    @Test
    void anExactOperandMakesTheOperationExact() throws Exception {
        assertEquals(10L, run(INT_CALC.formatted("Rational.toInt(DOWN, 1 / 2 * n.value + 3)"), 14L));
        assertEquals(7L, run(INT_CALC.formatted("Rational.toInt(DOWN, n.value * (1 / 2) + 0)"), 15L));
    }

    /** Including the coefficient the whole decision is about, reached through a name or written out.
     *  Extracting the binding changes what an author wrote and not what the arithmetic is. */
    @Test
    void aCoefficientReachedThroughANameIsTheCoefficient() throws Exception {
        String written = INT_CALC.formatted("Rational.toInt(FLOOR, -1 / 2 * n.value + 30)");
        String named = """
                module demo
                data N = Int
                behavior calc : (n: N) -> N constructs N
                let slope = -1 / 2
                let calc (n) = N { value = Rational.toInt(FLOOR, slope * n.value + 30) }
                """;
        assertEquals(20L, run(written, 20L));
        assertEquals(20L, run(named, 20L));
    }

    /** The negation answers the type it is given, so a model is not left writing `0 - r`. */
    @Test
    void theNegationOfAnExactValueIsExact() throws Exception {
        assertEquals(-3L, run(INT_CALC.formatted("Rational.toInt(DOWN, -(n.value / 2))"), 7L));
    }

    /** Equality and ordering are by exact value, and across the two numeric types where one side is
     *  exact. The Int/Decimal boundary is untouched: neither of those is exact on its own. */
    @Test
    void aComparisonWithAnExactSideIsByExactValue() throws Exception {
        assertEquals(1L, run(INT_CALC.formatted("if 1 == 2 / 2 then 1 else 0"), 0L));
        assertEquals(1L, run(INT_CALC.formatted("if 0.5m == 1 / 2 then 1 else 0"), 0L));
        assertEquals(1L, run(INT_CALC.formatted("if 1 < 3 / 2 then 1 else 0"), 0L));
        assertEquals(0L, run(INT_CALC.formatted("if 1 / 2 == 1 then 1 else 0"), 0L));
        refused(INT_CALC.formatted("if 1 == 1m then 1 else 0"));
        refused(INT_CALC.formatted("if 1 < 1m then 1 else 0"));
    }

    /** A model crosses from Int to Decimal through exact arithmetic, and only after an expression has
     *  visibly acquired one. */
    @Test
    void theTwoNumericTypesMeetOnlyThroughAnExactValue() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo
                data M = Decimal
                behavior calc : (m: M) -> M constructs M
                let calc (m) = M { value = Rational.toDecimal(2, HALF_UP, 1 / 1 + m.value) }
                """));
        refused("""
                module demo
                data M = Decimal
                behavior calc : (m: M) -> M constructs M
                let calc (m) = M { value = 1 + m.value }
                """);
    }

    /** A newtype's scalar division is not inherited: the dimension survives and the type does not, so
     *  there is no value of the base to wrap again. */
    @Test
    void aNewtypeIsNotDividedByAValueOfItsBase() {
        CompileException e = refused("""
                module demo
                data Yen = Int
                behavior calc : (y: Yen) -> Yen constructs Yen
                let calc (y) = y / 2
                """);
        assertTrue(e.getMessage().contains("no Int is left to wrap as Yen"), e.getMessage());
    }

    /** A Rational crosses no boundary: what a computation holds is not what a field stores or a
     *  behavior answers. */
    @Test
    void noPositionHoldsAnExactValue() {
        refused("""
                module demo
                data Ratio = { r: Rational }
                behavior calc : (x: Ratio) -> Ratio constructs Ratio
                let calc (x) = x
                """);
        refused("""
                module demo
                data R = Rational
                behavior calc : (r: R) -> R constructs R
                let calc (r) = r
                """);
    }

    /** The truncating quotient is still there, under the name that says what it does. */
    @Test
    void theTruncatingQuotientIsNamed() throws Exception {
        String model = INT_CALC.formatted("""
                match Int.truncatingDivide(n.value, 2) with
                    | Int as q -> q
                    | DivisionByZero -> 0""");
        assertEquals(3L, run(model, 7L));
        assertEquals(-1L, run(model, -3L));
    }

    /** And the two quotients are two numbers, which is why only one of them is named. */
    @Test
    void theExactQuotientAndTheTruncatedOneAreTwoNumbers() {
        assertEquals(Rational.of(BigInteger.valueOf(7), BigInteger.TWO),
                Rational.of(7).dividedBy(Rational.of(2)));
        assertEquals(new BigDecimal("3.5"), Rational.of(7).dividedBy(Rational.of(2)).asDecimal());
    }
}
