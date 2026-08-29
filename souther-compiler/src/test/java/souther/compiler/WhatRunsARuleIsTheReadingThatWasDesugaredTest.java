package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertAll;
import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A rule runs as the tree it is emitted from, and a comprehension is what tells the two apart.
 *
 * <p>The elaborator reads a comprehension into a one-element list — a carrier for the type, since
 * nothing emits one; the desugaring the emitter applies first reads it into the {@code if} that
 * honours the guard. Both type to a {@code List}, so which of them a rule came from is invisible to
 * everything except a value.
 *
 * <p>It was invisible in the compiler too, while the check elaborated a rule and dropped it and the
 * emitter elaborated the same rule again over the desugared tree. One reading held the declaration
 * and another ran (issue #1080). What holds it here is a row: a rule stating that nothing is kept
 * is kept by an input the guard excludes, and refused by one it does not — neither of which is true
 * of the carrier, whose list holds its element whatever the guard says.
 */
class WhatRunsARuleIsTheReadingThatWasDesugaredTest {

    private static final String MODULE = """
            module demo

            data Amount = Int

            behavior pick : (n: Int) -> Amount
                ensures empty = List.length([ n | n > 0 ]) == 0 && value.value == n

            let pick (n) = Amount(n)
            """;

    @Test
    void aRowTheGuardExcludesKeepsTheRule() {
        assertDoesNotThrow(() -> Compiler.compile(MODULE + """
                example pick
                  | "nothing is kept, and the rule says so" : (-1) -> Amount(-1)
                """),
                "the guard is false, so the comprehension keeps nothing and the rule holds");
    }

    @Test
    void aRowTheGuardAdmitsDoesNot() {
        CompileException refused = assertThrows(CompileException.class,
                () -> Compiler.compile(MODULE + """
                        example pick
                          | "one is kept, and the rule said none would be" : (1) -> Amount(1)
                        """));

        assertAll(
                () -> assertEquals("E1928", refused.diagnostics().get(0).code(),
                        "the row does not keep what the behavior states"),
                () -> assertEquals(1, refused.diagnostics().size(),
                        "said once: " + refused.diagnostics()));
    }
}
