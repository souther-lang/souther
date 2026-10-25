package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.RowToRun;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.RuleRequirement;
import souther.compiler.query.RuleSettlement;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row the run places at another rule is passed over, and the rule search goes on to the next
 * assignment of the values below.
 *
 * <p>The way for the rule says the container holds an element and that every element meets a
 * statement. A first assignment of the element that ignores the statement is a row the run sends
 * to the other rule; the rule is stood in by a later assignment whose element meets it.
 */
class ARowRefusedByTheRunIsPassedOverForTheNextAssignmentTest {

    private static final String A_NON_EMPTY_CONTAINER_OF_ELEMENTS_THAT_ALL_MEET = """
            module example.allmeet

            data Node = { v: Int, below: List<Node> }
            data Yes
            data No
            data Answer = Yes | No

            behavior f : (t: Node) -> Answer
            let f (t) =
                if t.v >= 3 && List.length(t.below) > 0 && List.all(c -> c.v >= 3, t.below)
                then Yes else No
            """;

    @Test
    void theRuleIsStoodInByARowWhoseChildMeetsTheStatement() {
        List<RuleSettlement> settled = settlementsOf(A_NON_EMPTY_CONTAINER_OF_ELEMENTS_THAT_ALL_MEET);

        List<RowToRun> witnesses = settled.stream()
                .map(RuleSettlement::requirement)
                .filter(RuleRequirement.Required.class::isInstance)
                .map(each -> ((RuleRequirement.Required) each).stoodBy())
                .toList();
        assertFalse(witnesses.isEmpty(), () -> "a rule is taken by a row: " + settled);
        assertEquals(settled.size(), witnesses.size(),
                () -> "every rule is taken by a row, the one that needs an element included: "
                        + settled);
        assertTrue(witnesses.stream().anyMatch(each ->
                        each.inputs().getFirst().text().contains("below = [Node")),
                () -> "and the rule that needs an element is taken by one: " + witnesses);
    }

    /**
     * No container here, so nothing is composed under a bound: the first assignment of the numbers
     * sends the row to the other rule, and the rule is taken by an assignment the walk reaches
     * after it.
     */
    @Test
    void aRuleTheFirstAssignmentDoesNotReachIsTakenByTheNext() {
        List<RuleSettlement> settled = settlementsOf("""
                module example.cap

                data Rate = Int
                    invariant nonNegative = value >= 0

                data Cap = Int
                    invariant nonNegative = value >= 0

                data Policy = { rate: Rate, cap: Cap }

                behavior f : (days: Int, policy: Policy) -> Int

                let f (days, policy) = {
                    let accrued = days * policy.rate.value

                    if accrued > policy.cap.value then policy.cap.value else accrued
                }
                """);

        assertEquals(settled.size(), requiredOf(settled).size(),
                () -> "every rule is taken by a row: " + settled);
    }

    @Test
    void everyElementOfAContainerThatHoldsSeveralMeetsTheStatement() {
        List<RuleSettlement> settled = settlementsOf(A_NON_EMPTY_CONTAINER_OF_ELEMENTS_THAT_ALL_MEET
                .replace("> 0", "> 1"));

        assertEquals(settled.size(), requiredOf(settled).size(),
                () -> "every rule is taken by a row: " + settled);
        assertTrue(requiredOf(settled).stream().anyMatch(each ->
                        each.inputs().getFirst().text().contains("below = [Node")
                                && each.inputs().getFirst().text().contains("}, Node")),
                () -> "and the rule that needs two elements is taken by a row holding two: "
                        + settled);
    }

    @Test
    void aStatementEveryElementMeetsAloneIsTakenByAnEmptyContainerToo() {
        List<RuleSettlement> settled = settlementsOf(A_NON_EMPTY_CONTAINER_OF_ELEMENTS_THAT_ALL_MEET
                .replace(" && List.length(t.below) > 0", ""));

        assertEquals(settled.size(), requiredOf(settled).size(),
                () -> "every rule is taken by a row: " + settled);
    }

    /**
     * The fields of an element that the type relates are chosen together: one at the least the way
     * leaves it and the other where the relation then leaves it, and not each at its own least.
     */
    @Test
    void anElementWhoseFieldsTheTypeRelatesMeetsTheStatementAndTheRelation() {
        List<RuleSettlement> settled = settlementsOf("""
                module example.related

                data Span = { lo: Int, hi: Int }
                    invariant total = lo + hi == 10
                data Holder = { spans: List<Span> }
                data Yes
                data No
                data Answer = Yes | No

                behavior f : (t: Holder) -> Answer
                let f (t) =
                    if List.length(t.spans) > 0
                        && List.all(s -> s.lo >= 3 && s.hi >= 3, t.spans)
                    then Yes else No
                """);

        assertEquals(settled.size(), requiredOf(settled).size(),
                () -> "every rule is taken by a row: " + settled);
    }

    private static List<RowToRun> requiredOf(List<RuleSettlement> settled) {
        return settled.stream()
                .map(RuleSettlement::requirement)
                .filter(RuleRequirement.Required.class::isInstance)
                .map(each -> ((RuleRequirement.Required) each).stoodBy())
                .toList();
    }

    /** What each rule of the body came to. */
    private static List<RuleSettlement> settlementsOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        List<RuleSettlement> out = AdequacyReport.of(compilation).modules().stream()
                .flatMap(module -> module.behaviors().stream())
                .filter(each -> "f".equals(each.name()))
                .flatMap(each -> each.ruleSettlements().values().stream())
                .map(each -> each.answer().settlement())
                .toList();
        assertFalse(out.isEmpty(), "the body decides, so it has rules a row is looked for at");
        return out;
    }
}
