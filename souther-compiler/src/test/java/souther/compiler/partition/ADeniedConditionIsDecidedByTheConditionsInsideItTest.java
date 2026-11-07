package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A condition that is another condition's truth denied is decided by the conditions inside it.
 *
 * <p>{@code guard Bool.not(a || b) else Done} is {@code if a || b then Done} said the other way
 * round, and its rules are the three ways the {@code ||} is decided: {@code a}, then {@code b} past
 * a false {@code a}, then neither. Read as one decision of its own, the denial had two rules — the
 * whole condition each way — and two rows meeting those two left the condition on {@code b} untold
 * from no condition at all.
 *
 * <p>Every spelling of the denial is held to the rules {@code plain} has, which is written with no
 * denial in it: the call, the comparisons against a written truth either way round, the denial
 * carried into each half, and an {@code if} with the truths written in its arms.
 */
class ADeniedConditionIsDecidedByTheConditionsInsideItTest {

    private static final String A_OR_B = "Set.contains(n, a) || Set.contains(n, b)";

    private static String model(String guarded, String examples) {
        return """
                module notdemo

                data Done
                data Fresh

                behavior denied : (n: Int, a: Set<Int>, b: Set<Int>) -> Done | Fresh
                let denied (n, a, b) = {
                    guard %s else Done
                    Fresh
                }

                behavior plain : (n: Int, a: Set<Int>, b: Set<Int>) -> Done | Fresh
                let plain (n, a, b) = if %s then Done else Fresh
                %s
                """.formatted(guarded, A_OR_B, examples);
    }

    /** The rules, each the conditions it consults in order and the way each was taken. */
    private static Set<String> rules(String source, String behavior) {
        return DecisionReadings.readToTheEnd(source, behavior).stream()
                .map(rule -> rule.inOrder().toString())
                .collect(Collectors.toSet());
    }

    @Test
    void everySpellingOfTheDenialHasTheRulesTheConditionHas() {
        List<String> spellings = List.of(
                "Bool.not(" + A_OR_B + ")",
                "Bool.not(Set.contains(n, a)) && Bool.not(Set.contains(n, b))",
                "(" + A_OR_B + ") == false",
                "(" + A_OR_B + ") /= true",
                "false == (" + A_OR_B + ")",
                "Bool.not((" + A_OR_B + ") == true)",
                "if " + A_OR_B + " then false else true",
                // Where a connective stops is where the truth of its left side is read, so these
                // tell a polarity carried the wrong way from the right one.
                "Set.contains(n, a) == false && Set.contains(n, b) == false",
                "false == Set.contains(n, a) && Set.contains(n, b) /= true",
                "Bool.not((Set.contains(n, a) /= false) || Set.contains(n, b))",
                "Bool.not(true == Set.contains(n, a) || Set.contains(n, b))");
        for (String guarded : spellings) {
            String source = model(guarded, "");
            Set<String> plain = rules(source, "plain");
            assertEquals(3, plain.size(), "a, then b past a false a, then neither");
            assertEquals(plain, rules(source, "denied"), guarded);
        }
    }

    /**
     * Two rows that meet neither half and the first half are short of the rule {@code b} decides,
     * and the row offered for it holds {@code n} in {@code b} alone. With the condition on
     * {@code b} deleted, the same two rows are short of nothing: the rows that tell the two bodies
     * apart are what the measure asks for.
     */
    @Test
    void theRowsOwedTellTheConditionOnTheSecondHalfFromNone() {
        String rows = """
                example denied
                    | (0, [], [])  -> Fresh
                    | (0, [0], []) -> Done
                """;
        String withB = model("Bool.not(" + A_OR_B + ")", rows);
        Compilation measured = measured(withB);
        assertEquals(1, uncoveredRulesOf(measured, "denied"),
                "the rule taken where a holds no n and b does");
        String offered = GeneratedRows.of(measured, measured.modules().get(0), "denied",
                SourceRendering.namedByIdentity(SourceLayouts.NONE)).text();
        assertTrue(offered.contains("| (0, [], [0]) -> <?>"), offered);

        String withoutB = model("Bool.not(Set.contains(n, a))", rows);
        assertEquals(0, uncoveredRulesOf(measured(withoutB), "denied"),
                "the control: a body with no condition on b owes no further row");
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static long uncoveredRulesOf(Compilation compilation, String behavior) {
        return AdequacyReport.of(compilation).findings().stream()
                .filter(each -> each.kind() == Adequacy.Kind.DECISION_RULE_UNCOVERED)
                .filter(each -> each.subject().toString().contains("name=" + behavior + "]"))
                .count();
    }
}
