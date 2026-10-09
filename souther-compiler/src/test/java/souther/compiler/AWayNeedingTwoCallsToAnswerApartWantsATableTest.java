package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.Generator;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.RuleRequirement;
import souther.compiler.query.RuleSearch;
import souther.compiler.query.RuleSettlement;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A way through two calls of one dependency that needs them to answer apart is a way this compiler
 * has no row for, and never a way the model rules out.
 *
 * <p>Two calls are two answers, so the way through the first denied and the second held is a way
 * of the decision. A row stands the dependency in with one value, which answers both alike — so no
 * row this compiler writes takes that way, and what it needs is a table answering each call. That
 * is something composing a row came to, and said as the model refusing the way it would tell an
 * author a counter cannot hand out a second number above the first.
 */
class AWayNeedingTwoCallsToAnswerApartWantsATableTest {

    private static final String MODEL = """
            module example.counter

            data Yes
            data No
            data Neither
            data Picked = Yes | No | Neither

            behavior nextId : () -> Int

            behavior pick : () -> Picked
                depends on nextId
            let pick (nextId) =
                if nextId() > 5 then Yes else if nextId() > 5 then No else Neither
            """;

    @Test
    void theWayThroughBothCallsAnsweringApartWantsATableAndIsNotRuledOut() {
        AdequacyReport.BehaviorReport pick = reportOf();

        assertEquals(3, pick.ruleSettlements().size(),
                () -> "the first call above five, the second, and neither: "
                        + pick.ruleSettlements());
        assertTrue(pick.ruleSettlements().values().stream()
                        .anyMatch(settled -> reasons(settled).contains(
                                Generator.UnresolvedCombination.Reason.A_TABLE_IS_WHAT_THIS_NEEDS)),
                () -> "the way through the two calls answering apart wants a table: "
                        + pick.ruleSettlements());
        assertFalse(pick.ruleSettlements().values().stream()
                        .anyMatch(settled -> settled.requirement()
                                instanceof RuleRequirement.Excluded),
                () -> "and no way is one the model rules out: " + pick.ruleSettlements());
    }

    /** The reasons a search that came to nothing came back with. */
    private static List<Generator.UnresolvedCombination.Reason> reasons(RuleSettlement settled) {
        return settled.search() instanceof RuleSearch.CameToNothing(var ways)
                ? ways.stream().map(Generator.UnresolvedCombination::reason).toList()
                : List.of();
    }

    private static AdequacyReport.BehaviorReport reportOf() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).modules().stream()
                .flatMap(module -> module.behaviors().stream())
                .filter(each -> "pick".equals(each.name()))
                .findFirst().orElseThrow(() -> new AssertionError("the model writes pick"));
    }
}
