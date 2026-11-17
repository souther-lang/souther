package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleCitation;
import souther.compiler.check.RuleRef;
import souther.compiler.check.RuleReportAnchor;
import souther.compiler.meaning.CaseCount;
import souther.compiler.meaning.CaseExpansion;
import souther.compiler.meaning.NumericallyConsistentWays;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Spelling;
import souther.compiler.meaning.WrittenLine;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.ModelOccurrences;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

import java.math.BigInteger;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A case worked out all the same, by what the numbers leave of the ways its choices stand for, is
 * kept beside the cases a line was not worked out for, and is not one of them: what a line not
 * worked out is told of its cases is those that were not, and nothing is told of a line whose
 * every case was.
 */
class ACaseWorkedOutIsNotOneTheLineWasNotWorkedOutForTest {

    private static final RuleCitation CITED = new RuleCitation.Written(
            new RuleRef.Comparison("g", new SourceConstructOrigin(
                    new WrittenOwner.Body("m", "g"), 1, 1, SourceConstruct.IF)),
            new RuleReportAnchor.ByTheReadingThatMetIt("Main", "g", 0));

    private static final CaseCount COUNTED = new CaseCount(
            new CaseCount.Ways.Exactly(BigInteger.valueOf(300)),
            new NumericallyConsistentWays.Counted.AtMost(BigInteger.valueOf(20)));

    private static ModelOccurrence construct(int ordinal) {
        return new ModelOccurrence(new SourceConstructOrigin(new WrittenOwner.Body("m", "g"),
                ordinal, 0, SourceConstruct.BINARY), ExpansionLineage.ORIGINAL);
    }

    private static CaseExpansion.CameTo cameTo(boolean workedOut, int ofTheParts) {
        return new CaseExpansion.CameTo(COUNTED,
                new CaseExpansion.Attributed(List.of(), ofTheParts, ofTheParts, List.of()),
                List.of(), workedOut);
    }

    private static CasesExpandedAtARule entry(CaseExpansion.CameTo... readings) {
        RulesWithNoLine.Gathered gathered = new RulesWithNoLine.Gathered();
        for (int at = 0; at < readings.length; at++) {
            gathered.expanded(CITED, ModelOccurrences.of(construct(10 + at)),
                    new CaseExpansion(new CaseExpansion.Which(new CaseExpansion.Line(
                            WrittenLine.THE_COMPARISON, Spelling.of("x")),
                            new Proposition.Always(true)), "g/x", "3", readings[at]));
        }
        return gathered.found().expanded().getFirst();
    }

    @Test
    void aCaseEveryReadingOfWhichWasWorkedOutIsToldOfAsNoneNotWorkedOut() {
        assertTrue(entry(cameTo(true, 4)).notWorkedOut().isEmpty());
    }

    @Test
    void aCaseNoReadingOfWhichWasWorkedOutIsToldOfAsItWas() {
        CasesExpandedAtARule stopped = entry(cameTo(false, 4));

        assertEquals(stopped, stopped.notWorkedOut().orElseThrow());
    }

    @Test
    void aCaseReadAtTwoCopiesIsToldOfByTheReadingsThatWereNotWorkedOut() {
        CasesExpandedAtARule both = entry(cameTo(true, 4), cameTo(false, 5));

        List<CasesExpandedAtARule.Reading> told = both.notWorkedOut().orElseThrow().readings();

        assertEquals(1, told.size());
        assertFalse(told.getFirst().cameTo().workedOut());
    }
}
