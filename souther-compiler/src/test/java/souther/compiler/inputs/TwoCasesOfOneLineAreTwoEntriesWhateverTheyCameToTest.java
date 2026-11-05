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
import souther.compiler.types.ModelOccurrences;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

import java.math.BigInteger;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a rule's line was told of its cases is kept one entry per case, as the reading told the
 * cases apart, and not one per count: two cases of one line that came to the same counts and the
 * same makers are two entries, and one case told twice is one.
 */
class TwoCasesOfOneLineAreTwoEntriesWhateverTheyCameToTest {

    private static final RuleCitation CITED = new RuleCitation.Written(
            new RuleRef.Comparison("g", new SourceConstructOrigin(
                    new WrittenOwner.Body("m", "g"), 1, 1, SourceConstruct.IF)),
            new RuleReportAnchor.ByTheReadingThatMetIt("Main", "g", 0));

    private static final CaseCount COUNTED = new CaseCount(
            new CaseCount.Ways.Exactly(BigInteger.valueOf(300)),
            new NumericallyConsistentWays.Counted.AtMost(BigInteger.valueOf(20)));

    private static CaseExpansion ofTheCase(Proposition condition) {
        return new CaseExpansion("g/x", Spelling.of("x"), condition, COUNTED,
                new CaseExpansion.Attributed(List.of(), 4, 4), List.of());
    }

    private static List<CasesExpandedAtARule> gathered(CaseExpansion... told) {
        RulesWithNoLine.Gathered gathered = new RulesWithNoLine.Gathered();
        for (CaseExpansion each : told) {
            gathered.expanded(CITED, ModelOccurrences.NONE, each);
        }
        return gathered.found().expanded();
    }

    @Test
    void twoCasesComingToTheSameAreTwoEntries() {
        assertEquals(2, gathered(ofTheCase(new Proposition.Always(true)),
                ofTheCase(new Proposition.Always(false))).size(),
                "one entry for each case the reading told apart");
    }

    @Test
    void oneCaseToldTwiceIsOneEntry() {
        assertEquals(1, gathered(ofTheCase(new Proposition.Always(true)),
                ofTheCase(new Proposition.Always(true))).size(),
                "the same case of the same line, told by two readers");
    }
}
