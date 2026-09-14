package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.query.PartitionEvidence;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A threshold on what a list comes to is asked for wherever the list is named from.
 *
 * <p>The rule a behavior exists for is the one the report has to reach. A total over a list is
 * compared against a number, and what a reader is owed is a row standing on that number, one below
 * it and one above — the same three a threshold on a field of the input is owed.
 *
 * <p>What decides it is nothing about the rule. Here the list arrives under a name a pattern gave
 * it, one step further from the parameter than a list read straight out of one, and the walk that
 * says which position the totalled values stand at has that one step more to take. A reading that
 * measures how far it has come rather than where it has been answers one of the two and not the
 * other, and the model that gets no answer is told its own rule is about a value nothing here works
 * out — a sentence about the model, said over a limit of this compiler.
 */
class ARuleOnWhatAListComesToIsAskedForHoweverTheListWasNamedTest {

    /** The list under a name of its own, taken apart where the behavior takes its parameter. */
    private static final String NAMED = """
            module example.total

            data 金額 = Int
                invariant value >= 0

            data 明細 = { 金額: 金額 }

            data 明細リスト = List<明細>
                invariant List.length(value) >= 1

            data 高額
            data 少額

            behavior 判定する : (明細: 明細リスト) -> 高額 | 少額

            let 合計 (明細リスト(件)): Int =
                List.sum(List.map(一件 -> 一件.金額.value, 件))

            let 判定する (明細) =
                if 合計(明細) >= 100000 then 高額 else 少額

            example 判定する
                | "ちょうど10万円なら高額" : (明細リスト([ 明細 { 金額 = 金額(100000) } ])) -> 高額
                | "1000円なら少額"        : (明細リスト([ 明細 { 金額 = 金額(1000) } ]))   -> 少額
            """;

    private static final String LINE = "List.sum(明細[*].金額) = 100000";

    private static Compilation compiled() {
        Compilation compilation = Compilation.ofSource(NAMED, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static BorderAssessment totalsLine() {
        Compilation compilation = compiled();
        Map<String, List<BorderAssessment>> lines =
                Adequacy.readingsOf(compilation.db(), compilation.modules().get(0));
        BorderAssessment line = lines.get("判定する").stream()
                .filter(each -> LINE.equals(each.label())).findFirst().orElse(null);
        assertNotNull(line, () -> "the threshold on the total is a line: "
                + lines.get("判定する").stream().map(BorderAssessment::label).toList());
        return line;
    }

    /** The line is drawn where the rule draws it: on the total of the amounts, at its number. */
    @Test
    void theThresholdOnTheTotalIsALine() {
        assertEquals(LINE, totalsLine().label());
    }

    /** The row the author already wrote — a list planning exactly the threshold — stands on it. */
    @Test
    void theRowPlanningExactlyTheThresholdStandsOnThePoint() {
        ItemAssessment.Owed on = totalsLine().owedAt(PointRole.ON);
        assertNotNull(on, "a row at the threshold is owed");
        assertTrue(on.hasRowWitness(), () -> "the row planning 100,000 stands at it: " + on);
    }

    /** And the point below it is owed and unmet, which is what this model is short of. */
    @Test
    void theRowBelowTheThresholdIsOwedAndMissing() {
        ItemAssessment.Owed off = totalsLine().owedAt(PointRole.OFF);
        assertNotNull(off, "a row below the threshold is owed");
        assertFalse(off.hasRowWitness(), () -> "no row is below it yet: " + off);
    }

    /** No position is left saying the rule is about a value made from it: the rule was read. */
    @Test
    void noPositionIsToldTheRuleIsAboutAValueMadeFromIt() {
        Compilation compilation = compiled();
        PartitionEvidence measured = compilation.db()
                .ask(new Adequacy.Coverage("example.total")).value().get("判定する");
        assertEquals(List.of(), measured.notRead().stream()
                .filter(each -> each.reason()
                        == UndividedPosition.Reason.RULE_ABOUT_A_DERIVED_VALUE)
                .map(PartitionEvidence.NotRead::at).toList());
    }
}
