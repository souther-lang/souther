package souther.architecture;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the pre-commit hook says about an operation written as the operand of an operation of
 * another precedence, held against what Error Prone's OperatorPrecedence says of the same source.
 *
 * <p>Each case is an expression, and the count of what Error Prone refuses in it is the count it
 * gives when it is run over it ({@link TheCommitHook}). Both counts are written down per case and
 * both are asserted, so a Checkstyle or an Error Prone that comes to answer differently fails here
 * and not in somebody's commit. The hook may refuse less than Error Prone and never more.
 */
class TheCommitHookRefusesAnOperandOfAnotherPrecedenceWhereErrorProneDoesTest {

    /** An expression, over the booleans {@code a} to {@code d} and the ints {@code x} to
     *  {@code z}, and how many times each of the two refuses something in it. */
    private record Case(String name, String expression, int errorProne, int hook) {
    }

    private static Case refusedByBoth(String name, String expression) {
        return new Case(name, expression, 1, 1);
    }

    private static Case acceptedByBoth(String name, String expression) {
        return new Case(name, expression, 0, 0);
    }

    private static final List<Case> CASES = List.of(
            refusedByBoth("an and under an or", "a || b && c"),
            refusedByBoth("an and under an or, on the left", "a && b || c"),
            refusedByBoth("an and under an or, on the next line", "a || b\n        && (c || d)"),
            new Case("two ands under one or", "a && b || c && d", 2, 2),
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
    void whatTheHookRefusesIsNeverMoreThanErrorProneRefuses() {
        for (Case each : CASES) {
            assertTrue(each.hook() <= each.errorProne(), each.name()
                    + ": a hook that refuses more than CI stops a commit CI accepts");
        }
    }

    @Test
    void eachCaseIsRefusedAsManyTimesAsErrorProneAndTheHookEachSay(@TempDir Path dir)
            throws Exception {
        Map<Path, Case> filed = new LinkedHashMap<>();
        for (int i = 0; i < CASES.size(); i++) {
            Case each = CASES.get(i);
            Path file = dir.resolve("Fixture" + i + ".java");
            Files.writeString(file, """
                    final class Fixture%d {
                        Object f(boolean a, boolean b, boolean c, boolean d, int x, int y, int z) {
                            return %s;
                        }
                    }
                    """.formatted(i, each.expression()));
            filed.put(file, each);
        }
        List<Path> files = List.copyOf(filed.keySet());

        Map<Path, Integer> byErrorProne = TheCommitHook.errorProneRefusals("OperatorPrecedence",
                dir, files);
        Map<Path, Integer> byTheHook = TheCommitHook.refusalsBy("OperatorPrecedence", files);

        List<String> disagreements = new ArrayList<>();
        for (Map.Entry<Path, Case> each : filed.entrySet()) {
            Case expected = each.getValue();
            int errorProne = byErrorProne.getOrDefault(each.getKey(), 0);
            int hook = byTheHook.getOrDefault(each.getKey(), 0);
            if (errorProne != expected.errorProne() || hook != expected.hook()) {
                disagreements.add(expected.name() + ": Error Prone refused " + errorProne
                        + " (written " + expected.errorProne() + "), the hook refused " + hook
                        + " (written " + expected.hook() + ")");
            }
        }
        assertEquals(List.of(), disagreements);
    }
}
