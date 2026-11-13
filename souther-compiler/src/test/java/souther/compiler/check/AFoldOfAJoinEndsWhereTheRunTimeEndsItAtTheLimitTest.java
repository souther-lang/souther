package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.types.BinOp;
import souther.runtime.ConstraintViolation;
import souther.runtime.Strings;
import souther.test.Nightly;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A folded {@code ++} answers what {@link Strings#append} answers at the longest text a
 * {@code String} holds, and is no fold one code point past it.
 *
 * <p>What the join answers within the limit is held by the sweep of small texts beside it, and where
 * the limit lies by the runtime's own tests at a small one; this asks only that the fold takes the
 * real limit from the run time, from both sides of it. One text of the longest length reaches both
 * with a single allocation, which is why it is nightly and not every run.
 */
@Nightly
class AFoldOfAJoinEndsWhereTheRunTimeEndsItAtTheLimitTest {

    @Test
    void aJoinFoldsAtTheLongestTextAndIsNoFoldOneCodePointPast() {
        String longest = "a".repeat((int) Strings.LONGEST_TEXT);

        assertEquals(Optional.of(Strings.append(longest, "")),
                ConstantAlgebra.binary(BinOp.CONCAT, longest, ""));

        assertThrows(ConstraintViolation.class, () -> Strings.append(longest, "b"));
        assertEquals(Optional.empty(), ConstantAlgebra.binary(BinOp.CONCAT, longest, "b"));
    }
}
