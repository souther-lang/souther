package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Weakening;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A verdict of {@code undetermined} says whether measuring again with more would answer any of it.
 *
 * <p>The model here is issue #1196's: a behavior that forks on a list computed from its input.
 * Every class of the position is derived and every one of them is covered, both arms are reached,
 * both outputs are specified — and the measure stays partial, because the comparison inside
 * {@code List.isEmpty} is about a value made from the position and nothing works out what it says
 * about the values there.
 *
 * <p>Nothing anybody writes closes that, and nothing any allowance changes either. Before this, the
 * report said {@code undetermined} and stopped, which is the same word it says over a row that did
 * not come back and a space too large to walk — so a person was left to work out for themselves
 * that measuring again would find exactly the same thing.
 */
class WhatKeepsAnUndeterminedVerdictOpenIsSaidTest {

    private static final String MODEL = """
            module probe.empty

            data 一般
            data 管理職
            data 役職 = 一般 | 管理職

            data 申請 = { 役職: 役職 }

            data 理由あり
            data 理由なし

            let 理由 (申請: 申請): List<役職> =
                match 申請.役職 with
                    | 一般   -> [ 一般 ]
                    | 管理職 -> []

            behavior 判定する : (申請: 申請) -> 理由あり | 理由なし
            let 判定する (申請) =
                if List.isEmpty(理由(申請)) then 理由なし else 理由あり

            example 判定する
                | "一般社員には理由がある" : (申請 { 役職 = 一般 })   -> 理由あり
                | "管理職には理由がない"   : (申請 { 役職 = 管理職 }) -> 理由なし
            """;

    private static AdequacyReport measured() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation);
    }

    /**
     * The verdict does not change, and that is the point.
     *
     * <p>{@code undetermined} means a measure that could have found a gap and was not made, which
     * is true here: the rule about the derived value may divide the position finer than the sum's
     * cases do, and nothing worked it out. What was missing was never the verdict.
     */
    @Test
    void theVerdictIsStillUndetermined() {
        AdequacyReport report = measured();

        assertEquals(AdequacyReport.AdequacyStatus.UNDETERMINED, report.adequacy(),
                () -> report.human(SourceNameResolver.identity()));
        assertTrue(report.adequacyGaps().isEmpty(),
                () -> "and no gap: there is nothing left to write " + report.adequacyGaps());
    }

    /** And what holds it open is one thing, which no allowance of this compiler's reaches. */
    @Test
    void whatKeepsItOpenIsOneThingAWiderRunDoesNotReach() {
        AdequacyReport report = measured();

        assertEquals(new AdequacyReport.UnderAWiderRun(0, 1), report.underAWiderRun(),
                () -> "what keeps it open: " + report.whatKeepsTheVerdictOpen().causes());
    }

    /**
     * And it is the rule inside {@code List.isEmpty}, named as such.
     *
     * <p>The count alone would pass over a model whose verdict was held open by something else
     * entirely, so the one fact is read as well: this is a reproduction and it is meant to keep
     * reproducing the thing it was written for.
     */
    @Test
    void andItIsTheRuleAboutTheValueTheListWasMadeFrom() {
        Weakening only = measured().whatKeepsTheVerdictOpen().causes().iterator().next();

        assertTrue(only instanceof Weakening.ModelReadingIncomplete it
                        && it.cause() instanceof souther.compiler.partition.ClosureGap.RuleUnread
                                rule
                        && rule.rule().why()
                                instanceof souther.compiler.inputs.BlockReason
                                        .RuleAboutADerivedValue,
                () -> "the comparison in `List.isEmpty` is about a value made from the position: "
                        + only);
    }

    /** And a person reading the report is told so, under the verdict. */
    @Test
    void theReportSaysItUnderTheVerdict() {
        String human = measured().human(SourceNameResolver.identity());

        assertTrue(human.contains("""
                adequacy: undetermined
                  what keeps it open
                    may change in a wider run     0
                    unaffected by a wider run     1
                """), human);
    }
}
