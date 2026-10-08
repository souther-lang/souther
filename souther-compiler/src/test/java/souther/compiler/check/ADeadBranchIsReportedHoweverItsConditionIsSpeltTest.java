package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.diag.Diagnostic;

import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Whether an arm of a fork is reached is what its condition means, and not how it is written.
 *
 * <p>A reader of the tree that runs meets a condition after the library's operations have been
 * expanded: {@code Bool.not} is a binding and a fork there, and {@code List.isEmpty} a call into the
 * expansion. What it takes in at a fork is what the condition states where the operations stand, so
 * two spellings of one condition are one answer about which arm a run can take.
 *
 * <p>Each pair is asked twice: under a rule that keeps the list non-empty, where one arm is dead, and
 * without it, where both are reached. The second is what says the first is about the rule and not
 * about the spelling.
 */
class ADeadBranchIsReportedHoweverItsConditionIsSpeltTest {

    private static String probe(boolean nonEmpty, String condition) {
        return """
                module probe

                data Box = { xs: List<Int> }
                %s
                behavior f : (x: Box) -> Int
                let f (x) = if %s then 2 else 1
                """.formatted(nonEmpty ? "    invariant List.length(xs) >= 1\n" : "", condition);
    }

    private static boolean deadBranch(String source) {
        return Compiler.compileWithWarnings(source).warnings().stream()
                .map(Diagnostic::code)
                .anyMatch("E1327"::equals);
    }

    /** Whether each spelling reports a dead branch, with the rule and without it. */
    private static Map<String, List<Boolean>> asked(String... spellings) {
        Map<String, List<Boolean>> out = new TreeMap<>();
        for (String each : spellings) {
            out.put(each, List.of(deadBranch(probe(true, each)), deadBranch(probe(false, each))));
        }
        return out;
    }

    private static Map<String, List<Boolean>> all(List<Boolean> answer, String... spellings) {
        Map<String, List<Boolean>> out = new TreeMap<>();
        for (String each : spellings) {
            out.put(each, answer);
        }
        return out;
    }

    @Test
    void anEmptinessCheckIsTheSizeComparisonItMeans() {
        String[] spellings = {"List.isEmpty(x.xs)", "List.length(x.xs) == 0"};
        assertEquals(all(List.of(true, false), spellings), asked(spellings),
                "a list the rule keeps non-empty is never empty, however that is asked");
    }

    @Test
    void aDenialIsTheComparisonWithFalse() {
        String[] spellings = {"Bool.not(List.isEmpty(x.xs))", "List.isEmpty(x.xs) == false",
            "Bool.not(List.length(x.xs) == 0)", "List.length(x.xs) /= 0"};
        assertEquals(all(List.of(true, false), spellings), asked(spellings),
                "a denial written as an operation is the comparison written with an operator");
    }

    @Test
    void aWitnessTheRuleProvidesSettlesTheFork() {
        String[] spellings = {"List.any(e -> true, x.xs)", "List.length(x.xs) >= 1"};
        assertEquals(all(List.of(true, false), spellings), asked(spellings),
                "an element the closure holds of exists wherever an element does, so where the rule"
                        + " says there is one the `else` is dead");
    }
}
