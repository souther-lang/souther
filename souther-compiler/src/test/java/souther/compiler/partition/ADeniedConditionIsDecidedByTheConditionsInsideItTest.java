package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
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
 * <p>Every spelling of the denial is held to what {@code plain} has, which is written with no denial
 * in it, from the rules to the rows: the rules are the same, each step of each is seen where the
 * call deciding it answers and never at an arm of the guard, two rows leave the rule {@code b}
 * decides owed and offer the row for it, and the three rows meeting the three ways owe nothing.
 */
class ADeniedConditionIsDecidedByTheConditionsInsideItTest {

    private static final String A_OR_B = "Set.contains(n, a) || Set.contains(n, b)";

    /** The call, the comparisons against a written truth either way round, the denial carried into
     *  each half, and an {@code if} with the truths written in its arms. The last four put a
     *  restatement where a connective stops, which is where the truth of its left side is read, so
     *  they tell a polarity carried the wrong way from the right one. */
    private static final List<String> SPELLINGS = List.of(
            "Bool.not(" + A_OR_B + ")",
            "Bool.not(Set.contains(n, a)) && Bool.not(Set.contains(n, b))",
            "(" + A_OR_B + ") == false",
            "(" + A_OR_B + ") /= true",
            "false == (" + A_OR_B + ")",
            "Bool.not((" + A_OR_B + ") == true)",
            "if " + A_OR_B + " then false else true",
            "Set.contains(n, a) == false && Set.contains(n, b) == false",
            "false == Set.contains(n, a) && Set.contains(n, b) /= true",
            "Bool.not((Set.contains(n, a) /= false) || Set.contains(n, b))",
            "Bool.not(true == Set.contains(n, a) || Set.contains(n, b))");

    /**
     * {@code denied} guarded by {@code guarded} with two rows, {@code deniedAll} the same with a
     * third, and {@code plain} the condition written with no denial: one module, so one compile
     * answers every reading of the three.
     */
    private static String model(String guarded) {
        return model(guarded, "Done");
    }

    /** As above, where the third row of {@code deniedAll} states {@code third}. */
    private static String model(String guarded, String third) {
        return """
                module notdemo

                data Done
                data Fresh

                behavior denied : (n: Int, a: Set<Int>, b: Set<Int>) -> Done | Fresh
                let denied (n, a, b) = {
                    guard %1$s else Done
                    Fresh
                }

                behavior deniedAll : (n: Int, a: Set<Int>, b: Set<Int>) -> Done | Fresh
                let deniedAll (n, a, b) = {
                    guard %1$s else Done
                    Fresh
                }

                behavior plain : (n: Int, a: Set<Int>, b: Set<Int>) -> Done | Fresh
                let plain (n, a, b) = if %2$s then Done else Fresh

                example denied
                    | (0, [], [])  -> Fresh
                    | (0, [0], []) -> Done

                example deniedAll
                    | (0, [], [])  -> Fresh
                    | (0, [0], []) -> Done
                    | (0, [], [0]) -> %3$s
                """.formatted(guarded, A_OR_B, third);
    }

    @Test
    void everySpellingOfTheDenialHasTheRulesTheConditionHas() {
        for (String guarded : SPELLINGS) {
            DecisionReadings.Compiled compiled = DecisionReadings.compiled(model(guarded));
            Set<String> plain = rules(compiled, "plain");
            assertEquals(3, plain.size(), "a, then b past a false a, then neither");
            assertEquals(plain, rules(compiled, "denied"), guarded);
            assertSeenWhereTheCallsAnswer(compiled, "denied", guarded);
        }
    }

    /**
     * Two rows that meet neither half and the first half are short of the rule {@code b} decides,
     * and the row offered for it holds {@code n} in {@code b} alone; with that row added, the rows
     * are short of nothing, which is each run placed at the rule it took.
     *
     * <p>Asked of the call and of the denials a connective joins, which are the two ways the
     * denial's truth reaches the guard. What a row is placed by is the rules and where each of their
     * steps is seen, which every spelling above is held to.
     */
    @Test
    void theRowsOwedAreTheRowsThatTellEveryWayApart() {
        for (String guarded : List.of(SPELLINGS.get(0), SPELLINGS.get(1))) {
            Compilation measured = measured(model(guarded));
            assertEquals(1, uncoveredRulesOf(measured, "denied"),
                    () -> guarded + ": the rule taken where a holds no n and b does");
            String offered = GeneratedRows.of(measured, measured.modules().get(0), "denied",
                    SourceRendering.namedByIdentity(SourceLayouts.NONE)).textInEnglish();
            // The rows are set out in columns, so what one row is padded with turns on the rest.
            assertTrue(offered.replaceAll(" +", " ").contains("| (0, [], [0]) -> <?>"),
                    () -> guarded + ": " + offered);
            assertEquals(0, uncoveredRulesOf(measured, "deniedAll"),
                    () -> guarded + ": a row for each way, and each placed at its rule");
        }
    }

    /** The control: with the condition on {@code b} deleted, the two rows owe nothing, so what the
     *  measure asks for above is the condition on {@code b} and not a row of any kind. */
    @Test
    void aBodyWithNoConditionOnTheSecondHalfOwesNoFurtherRow() {
        assertEquals(0, uncoveredRulesOf(
                measured(model("Bool.not(Set.contains(n, a))", "Fresh")), "denied"));
    }

    /**
     * A denial of a value whose truth no way of it says — a position handed in, a field of one — is
     * read as the value built out of it, which is where a truth it comes out either way is asked
     * for: its rules, and where each is seen, are those of the same decision written with no denial.
     */
    @Test
    void aDenialOfATruthNoWayHoldsIsReadAsTheDecisionWithoutIt() {
        for (String truth : List.of("flagged", "r.flag")) {
            String source = """
                    module notdemo

                    data Done
                    data Fresh
                    data R = { flag: Bool }

                    behavior denied : (flagged: Bool, r: R) -> Done | Fresh
                    let denied (flagged, r) = {
                        guard Bool.not(%s) else Done
                        Fresh
                    }

                    behavior plain : (flagged: Bool, r: R) -> Done | Fresh
                    let plain (flagged, r) = if %s then Done else Fresh
                    """.formatted(truth, truth);
            DecisionReadings.Compiled compiled = DecisionReadings.compiled(source);
            Set<String> plain = rules(compiled, "plain");
            assertEquals(2, plain.size(), truth + " holding, and failing");
            assertEquals(plain, rules(compiled, "denied"), truth);
            assertEquals(seenAs(compiled, "plain"), seenAs(compiled, "denied"), truth);
        }
    }

    /** What kind of place each step of each rule is seen at. */
    private static Set<List<String>> seenAs(DecisionReadings.Compiled compiled, String behavior) {
        return compiled.of(behavior).found().stream()
                .map(rule -> rule.shownBy().stream()
                        .map(shown -> shown.getClass().getSimpleName()).toList())
                .collect(Collectors.toSet());
    }

    /** The rules, each the conditions it consults in order and the way each was taken. */
    private static Set<String> rules(DecisionReadings.Compiled compiled, String behavior) {
        return compiled.readToTheEnd(behavior).stream()
                .map(rule -> rule.inOrder().toString())
                .collect(Collectors.toSet());
    }

    /**
     * Every step of every rule seen where one of the two calls answers, and both calls among them:
     * what a report says decides the rule is the call, and not an arm of what it guards.
     */
    private static void assertSeenWhereTheCallsAnswer(DecisionReadings.Compiled compiled,
                                                      String behavior, String what) {
        Set<Object> calls = new HashSet<>();
        for (DecisionReading.Ruled rule : compiled.of(behavior).found()) {
            for (ShownBy shown : rule.shownBy()) {
                ShownBy.AtAnOutcome atACall = assertInstanceOf(ShownBy.AtAnOutcome.class, shown,
                        () -> what + ": seen where a call answers, not " + shown);
                calls.add(atACall.construct());
            }
        }
        assertEquals(2, calls.size(), () -> what + ": the two calls of Set.contains: " + calls);
    }

    private static Compilation measured(String source) {
        return ACompiledModel.measured(source, Adequacy.Asked.fullReport());
    }

    private static long uncoveredRulesOf(Compilation compilation, String behavior) {
        return AdequacyReport.of(compilation).findings().stream()
                .filter(each -> each.kind() == Adequacy.Kind.DECISION_RULE_UNCOVERED)
                .filter(each -> each.subject().toString().contains("name=" + behavior + "]"))
                .count();
    }
}
