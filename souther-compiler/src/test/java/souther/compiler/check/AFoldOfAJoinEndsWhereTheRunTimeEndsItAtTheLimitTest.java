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
 * {@code String} holds, and is no fold where the run ends there.
 *
 * <p>Nightly, for what it costs: the texts are the real limit long, a quarter of a gigabyte each.
 */
@Nightly
class AFoldOfAJoinEndsWhereTheRunTimeEndsItAtTheLimitTest {

    private static final int LONGEST = (int) Strings.LONGEST_TEXT;

    @Test
    void aJoinOfExactlyTheLongestTextFoldsAsTheRunTimeAnswers() {
        String a = "a".repeat(LONGEST - 1);
        assertEquals(Optional.of(Strings.append(a, "b")), ConstantAlgebra.binary(BinOp.CONCAT, a, "b"));
    }

    @Test
    void aJoinOneCodePointPastIsNoFoldWhereTheRunTimeEnds() {
        String a = "a".repeat(LONGEST);
        assertThrows(ConstraintViolation.class, () -> Strings.append(a, "b"));
        assertEquals(Optional.empty(), ConstantAlgebra.binary(BinOp.CONCAT, a, "b"));
    }
}
