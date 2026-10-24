package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.diag.Diagnostic;

import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * An arm whose condition only values past where their type stops satisfy is one nothing reaches.
 *
 * <p>Over the integers {@code b >= 1} and {@code a - b >= M}, with {@code M} the greatest {@code Int},
 * have solutions, and none of them is an {@code Int}. Each condition is asked in both orders, since
 * what a path knows must not depend on which half was read first, and beside a neighbour that is
 * reached, which says the answer is about the type's end and not about the shape of the condition.
 */
class AWayOnlyValuesPastWhereTheirTypeStopsTakeIsReachedByNothingTest {

    private static final String MAX = "9223372036854775807";

    private static boolean deadBranch(String condition) {
        String source = """
                module probe

                behavior m : (a: Int, b: Int) -> Bool
                let m (a, b) = if %s then true else false
                """.formatted(condition);
        return Compiler.compileWithWarnings(source).warnings().stream()
                .map(Diagnostic::code)
                .anyMatch("E1327"::equals);
    }

    private static Map<String, Boolean> asked(String... conditions) {
        Map<String, Boolean> out = new TreeMap<>();
        for (String each : conditions) {
            out.put(each, deadBranch(each));
        }
        return out;
    }

    @Test
    void aSumPastTheGreatestIntIsReachedByNothingWhicheverHalfIsReadFirst() {
        List<String> past = List.of(
                "b >= 1 && a - b >= " + MAX,
                "a - b >= " + MAX + " && b >= 1");
        Map<String, Boolean> expected = new TreeMap<>();
        past.forEach(each -> expected.put(each, true));
        assertEquals(expected, asked(past.toArray(String[]::new)));
    }

    @Test
    void theNeighboursThatStayInsideTheTypeAreReached() {
        List<String> inside = List.of(
                "b >= 1 && a - b >= 9223372036854775806",
                "b >= 0 && a - b >= " + MAX);
        Map<String, Boolean> expected = new TreeMap<>();
        inside.forEach(each -> expected.put(each, false));
        assertEquals(expected, asked(inside.toArray(String[]::new)));
    }
}
