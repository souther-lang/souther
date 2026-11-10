package souther.architecture;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import souther.architecture.TheCommitHook.Filed;

import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static souther.architecture.TheCommitHook.Filed.acceptedByBoth;
import static souther.architecture.TheCommitHook.Filed.refusedByBoth;

/**
 * What the pre-commit hook says about an operation written as the operand of an operation of
 * another precedence, held against what Error Prone's OperatorPrecedence says of the same source.
 *
 * <p>Each case is an expression, and what Error Prone refuses in it is what it gives when it is run
 * over it ({@link TheCommitHook}). The hook may refuse less than Error Prone and never more.
 */
class TheCommitHookRefusesAnOperandOfAnotherPrecedenceWhereErrorProneDoesTest {

    /** Each expression is over the booleans {@code a} to {@code d} and the ints {@code x} to
     *  {@code z}. */
    private static final List<Filed> CASES = List.of(
            refusedByBoth("an and under an or", "a || b && c"),
            refusedByBoth("an and under an or, on the left", "a && b || c"),
            refusedByBoth("an and under an or, on the next line", "a || b\n        && (c || d)"),
            refusedByBoth("two ands under one or", "a && b || c && d"),
            refusedByBoth("an and inside an argument", "Boolean.valueOf(a && b || c)"),
            acceptedByBoth("an and in parentheses", "a || (b && c)"),
            acceptedByBoth("an or in parentheses", "(a || b) && c"),
            acceptedByBoth("an and in two pairs of parentheses", "a || ((b && c))"),
            acceptedByBoth("the same operator", "a || b || c"),
            acceptedByBoth("a comparison under an and", "x == y && a"),
            acceptedByBoth("an or compared", "a == (b || c)"),
            acceptedByBoth("a negated and under an or", "a || !(b && c)"),

            refusedByBoth("a bitwise and under an and", "a && b & c"),
            refusedByBoth("a bitwise and under a bitwise or", "(x & y | z) > 0"),
            refusedByBoth("an exclusive or under a bitwise or", "(x ^ y | z) > 0"),
            refusedByBoth("a bitwise or under an or", "a || b | c"),
            acceptedByBoth("the same bitwise operator", "(x | y | z) > 0"),

            refusedByBoth("a sum under a shift", "(x + y << z) > 0"),
            refusedByBoth("a difference under an unsigned shift", "(x - y >>> z) > 0"),
            refusedByBoth("a product under a shift, on the right", "(x >> y * z) > 0"),
            acceptedByBoth("a shift in parentheses under a sum", "((x << y) + z) > 0"),
            acceptedByBoth("a product under a sum", "x * y + z > 0"));

    @Test
    void theHookStandsToErrorProneAsEachCaseSays(@TempDir Path dir) throws Exception {
        assertEquals(List.of(), TheCommitHook.disagreements(dir, "OperatorPrecedence",
                "OperatorPrecedence", CASES, (i, expression) -> """
                        final class Fixture%d {
                            Object f(boolean a, boolean b, boolean c, boolean d, int x, int y, int z) {
                                return %s;
                            }
                        }
                        """.formatted(i, expression)));
    }
}
