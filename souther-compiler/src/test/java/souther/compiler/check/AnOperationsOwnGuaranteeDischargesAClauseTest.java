package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What an operation guarantees of its own result holds wherever the call is written, so a
 * construction standing over one owes nothing the operation has already established. The guard such
 * a report would ask for restates the operation.
 *
 * <p>Every construction here is written in a behavior, which is where a construction is judged: a
 * value definition builds its result outside any path, and nothing is read of one.
 */
class AnOperationsOwnGuaranteeDischargesAClauseTest {

    private static final String TYPES = """
            module demo
            data NonNeg = Int
                invariant value >= 0
            data NonNegD = Decimal
                invariant value >= 0.0m
            data Bad
            """;

    private static List<String> warningsOf(String module) {
        return Compiler.compileWithWarnings(module).warnings().stream()
                .filter(d -> d.severity() == Severity.WARNING)
                .map(Diagnostic::code)
                .toList();
    }

    @Test
    void aDecimalMadeFromAnIntIsThatNumber() {
        assertEquals(List.of(), warningsOf(TYPES + """
                behavior widen : (n: Int) -> NonNegD | Bad constructs NonNegD, Bad
                let widen (n) = {
                    guard n >= 0
                        else Bad
                    NonNegD(Decimal.fromInt(n))
                }
                """));
    }

    @Test
    void anAbsoluteValueIsNeverNegative() {
        assertEquals(List.of(), warningsOf(TYPES + """
                behavior distance : (x: Int) -> NonNeg constructs NonNeg
                let distance (x) = NonNeg(Int.abs(x))
                """));
    }

    @Test
    void aRemainderIsNeverNegative() {
        assertEquals(List.of(), warningsOf(TYPES + """
                behavior wrap : (x: Int) -> NonNeg constructs NonNeg
                let wrap (x) = NonNeg(Int.floorMod(x, 100))
                """));
    }

    @Test
    void aRemainderIsBelowADivisorReadAsAConstant() {
        assertEquals(List.of(), warningsOf(TYPES + """
                data Pct = Int
                    invariant value >= 0 && value <= 100
                behavior wrap : (x: Int) -> Pct constructs Pct
                let wrap (x) = Pct(Int.floorMod(x, 100))
                """));
    }

    @Test
    void aRemainderByADivisorThatIsNotAConstantIsNotBoundedAbove() {
        assertEquals(List.of("E2011"), warningsOf(TYPES + """
                data Pct = Int
                    invariant value >= 0 && value <= 100
                behavior wrap : (x: Int, k: Int) -> Pct constructs Pct
                let wrap (x, k) = Pct(Int.floorMod(x, k))
                """));
    }

    @Test
    void aRoundedDecimalIsWithinOneOfWhatItRounds() {
        assertEquals(List.of(), warningsOf(TYPES + """
                data AtLeastTen = Int
                    invariant value >= 10
                behavior whole : (d: Decimal) -> AtLeastTen | Bad constructs AtLeastTen, Bad
                let whole (d) = {
                    guard d >= 11.0m
                        else Bad
                    AtLeastTen(Decimal.toInt(HALF_UP, d))
                }
                """));
    }

    @Test
    void aValueNoOperationBoundsIsStillReported() {
        assertEquals(List.of("E2011"), warningsOf(TYPES + """
                behavior plain : (x: Int) -> NonNeg constructs NonNeg
                let plain (x) = NonNeg(x)
                """));
    }
}
