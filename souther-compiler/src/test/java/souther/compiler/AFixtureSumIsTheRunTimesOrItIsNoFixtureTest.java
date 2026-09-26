package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.CompileException;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A fixture holds Souther values, so the arithmetic a row writes answers what the run time answers
 * for the same expression: the value, or that there is none. An {@code Int} sum past 64 bits aborts
 * at run time, so a row whose input is one is a row that cannot be run and not a row about the number
 * the sum would wrap to.
 */
class AFixtureSumIsTheRunTimesOrItIsNoFixtureTest {

    private static String rowWith(String n) {
        return """
                module demo

                data In = { n: Int }

                behavior run : (i: In) -> Int

                let run (i) = 42

                example run
                    | "a sum" : (In { n = %s }) -> 42
                """.formatted(n);
    }

    @Test
    void aSumInsideTheRangeIsTheSum() {
        assertDoesNotThrow(() -> Compiler.compile(rowWith("9223372036854775806 + 1")));
    }

    @Test
    void anIntSumPastTheRangeIsARowThatCannotBeRun() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compile(rowWith("9223372036854775807 + 1")));
        assertEquals("E1903", e.diagnostic().code());
    }

    @Test
    void anIntProductPastTheRangeIsARowThatCannotBeRun() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compile(rowWith("4611686018427387904 * 2")));
        assertEquals("E1903", e.diagnostic().code());
    }
}
