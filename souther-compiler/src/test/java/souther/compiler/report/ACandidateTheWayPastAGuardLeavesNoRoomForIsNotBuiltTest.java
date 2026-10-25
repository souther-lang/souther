package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.test.Nightly;

import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row stopped at a guard is looked for past it among the assignments nearest the row, and a
 * candidate whose classes leave what the way past the guard asks no room is not one the search
 * builds: what it is allowed to build is not spent on candidates nothing can be built from.
 *
 * <p>Spent that way, a guard on a field that comes after one of many classes was never reached.
 * The candidates that move the first field come first and fill the allowance, and the row offered
 * stopped at the guard whatever the guarded field's classes were.
 *
 * <p>Nightly, for what it costs: the field has to have more classes than a search is allowed to
 * build candidates, and generating rows for every one of them is most of a minute. A model with
 * fewer reaches the guarded field inside the allowance whether or not the candidates ahead of it
 * are built, so none asks the question.
 */
@Nightly
class ACandidateTheWayPastAGuardLeavesNoRoomForIsNotBuiltTest {

    /** More thresholds on one field than a search is allowed candidates for. */
    private static final int THRESHOLDS = 72;

    /** How many thresholds each helper chain holds, so that no body is written deeper than it may. */
    private static final int PER_HELPER = 8;

    private static String model() {
        StringBuilder helpers = new StringBuilder();
        int helperCount = THRESHOLDS / PER_HELPER;
        for (int k = 1; k <= helperCount; k++) {
            int top = THRESHOLDS - (k - 1) * PER_HELPER;
            String chain = IntStream.range(0, PER_HELPER)
                    .mapToObj(i -> "if x > " + (top - i) + " then " + (top - i) + " else ")
                    .collect(Collectors.joining());
            helpers.append("let rung").append(k).append(" (x: Int): Int = ").append(chain)
                    .append(k < helperCount ? "rung" + (k + 1) + "(x)" : "0").append('\n');
        }
        return """
                module example.wide

                data Done = { n: Int }
                data Refused

                data Wide = { many: Int, one: Int, days: Int }

                %s
                behavior judge : (w: Wide) -> Done | Refused
                    constructs Done

                let judge (w) = {
                    guard w.days >= 17 else Refused
                    Done { n = rung1(w.many) + (if w.one > 0 then 1 else 0) }
                }
                """.formatted(helpers);
    }

    private static String offered(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        return GeneratedRows.of(compilation, null, null,
                new SourceRendering(id -> "wide.sou", compilation.texts())).text();
    }

    @Test
    void theRowOfferedGoesPastAGuardOnAFieldAfterOneOfManyClasses() {
        String block = offered(model());
        // The class below the guard is the one row that stops at it, and says nothing else was
        // left to try. A row for any other class goes past it.
        List<String> stopping = block.lines().filter(line -> line.contains("stops at the guard"))
                .toList();
        assertFalse(stopping.isEmpty(), block);
        assertTrue(stopping.stream().allMatch(line -> line.contains("`w.days=x < 17`")),
                () -> "a row for a class of another field stopped at the guard: " + stopping);
        assertTrue(block.contains("many = 1, one = 0, days = 17"), block);
    }
}
