package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.CompileException;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A chain of values in which each names the one before it twice is as long as the source wrote it,
 * and an {@code invariant} that names the last of them is read as long as that. The work that
 * takes is held by {@code AChainOfLetsIsReadInWorkThatGrowsWithItsLengthTest}; what is asked here
 * is what the chain comes to where its length matters to the answer.
 */
class AValueNamedTwiceInAnInvariantIsNotCopiedTwiceTest {

    private static String chain(int links, String first, String operator, String type) {
        StringBuilder source = new StringBuilder("module m exposing ( D, f )\n\nlet c0 = " + first + "\n");
        for (int at = 1; at <= links; at++) {
            source.append("let c%d = c%d %s c%d\n".formatted(at, at - 1, operator, at - 1));
        }
        source.append("""

                data D = %s
                    invariant value > c%d

                behavior f : (d: D) -> Int
                let f (d) = 1
                """.formatted(type, links));
        return source.toString();
    }

    /**
     * A value built once for the clause holds what its body wrote, and a newtype's {@code T(v)}
     * written there is the construction it means wherever the clause is read — so a clause that
     * reaches one through a value is refused as one that constructs, as it is where it writes it.
     */
    @Test
    void aValueTheClauseHoldsIsReadAsTheConstructionItsBodyWrites() {
        String source = """
                module m exposing ( D, f )

                data Cap = Int
                    invariant value > 0

                let cap = Cap(10)

                data D = Int
                    invariant value < cap.value && value > 0 - cap.value

                behavior f : (n: Int) -> Int
                    constructs D
                let f (n) = if D(n) as d then 1 else 0
                """;

        CompileException refused = assertThrows(CompileException.class,
                () -> Compiler.compile(source));
        assertEquals("E1105", refused.diagnostic().code(), refused.getMessage());
    }

    @Test
    void aChainOfDecimalsTakenPastTheEndOfTheScaleRangeIsCompiled() {
        String source = chain(34, "0.1m", "*", "Decimal");

        assertDoesNotThrow(() -> Compiler.compile(source));
    }

    @Test
    void aChainOfDecimalsSquaredIntoTheEndOfTheScaleRangeIsCompiled() {
        String source = chain(30, "0.1m", "*", "Decimal");

        assertDoesNotThrow(() -> Compiler.compile(source));
    }
}
