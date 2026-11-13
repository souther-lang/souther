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
 * A folded {@code ++} is no fold where {@link Strings#append} ends the run at the longest text a
 * {@code String} holds.
 *
 * <p>What the join answers within the limit is held by the sweep of small texts beside it, and where
 * the limit lies by the runtime's own tests at a small one; this asks only that the fold takes the
 * real limit from the run time. One text joined to itself reaches it with a single allocation of
 * half the limit, which is why it is nightly and not every run.
 */
@Nightly
class AFoldOfAJoinEndsWhereTheRunTimeEndsItAtTheLimitTest {

    @Test
    void aJoinOneCodePointPastIsNoFoldWhereTheRunTimeEnds() {
        String half = "a".repeat((int) (Strings.LONGEST_TEXT / 2 + 1));
        assertThrows(ConstraintViolation.class, () -> Strings.append(half, half));
        assertEquals(Optional.empty(), ConstantAlgebra.binary(BinOp.CONCAT, half, half));
    }
}
