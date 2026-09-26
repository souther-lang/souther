package souther.compiler;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;

/**
 * A {@code Decimal} product whose scale leaves the signed 32-bit range is a value the language has
 * none for, and the compiler meets it while reasoning about the program, not while running it. What
 * it says about such a program is up to the phase that meets it; that it says something and does not
 * stop with a {@code java.math} exception is what every phase owes.
 */
class ADecimalProductOutOfRangeIsNotAnInternalErrorTest {

    /** A chain of squarings from {@code seed}: the scale doubles at each, so 32 of them leave the
     *  range wherever it starts. */
    private static String squaredThirtyTwoTimes(String seed) {
        StringBuilder chain = new StringBuilder();
        chain.append("    let s0 = ").append(seed).append('\n');
        for (int i = 1; i <= 32; i++) {
            chain.append("    let s").append(i).append(" = s").append(i - 1)
                    .append(" * s").append(i - 1).append('\n');
        }
        return """
                module m exposing ( g )

                behavior g : (n: Int) -> Int
                let g (n) = {
                %s    if s32 == 0.0m then 1 else n
                }
                """.formatted(chain);
    }

    @Test
    void aProductWhoseScaleLeavesTheRangeIsNotAnInternalError() {
        assertDoesNotThrow(() -> Compiler.compile(squaredThirtyTwoTimes("0.1m")));
    }

    @Test
    void aValueTheModuleStatesBySquaringIsNotAnInternalError() {
        StringBuilder values = new StringBuilder("let c0 = 0.1m\n");
        for (int i = 1; i <= 32; i++) {
            values.append("let c").append(i).append(" = c").append(i - 1)
                    .append(" * c").append(i - 1).append('\n');
        }
        assertDoesNotThrow(() -> Compiler.compile("""
                module m exposing ( g )

                %s
                behavior g : (n: Int) -> Int
                let g (n) = if c32 == 0.0m then 1 else n
                """.formatted(values)));
    }
}
