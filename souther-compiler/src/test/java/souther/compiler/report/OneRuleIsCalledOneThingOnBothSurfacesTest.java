package souther.compiler.report;

import souther.compiler.report.AdequacyReport;
import souther.compiler.types.WrittenOwner;
import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleCitation;
import souther.compiler.check.RuleRef;
import souther.compiler.types.CoverageConstruct;
import souther.compiler.types.CoverageOrigin;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A rule with no name is called the same thing by a reader and by a document.
 *
 * <p>Two surfaces and one rule. A reader is sent to a comparison by where it is written and sees
 * {@code comparison@…}; a document groups the same rule under a word of its own. While every
 * comparison a rule was read off stood in the condition of a {@code guard} or an {@code if}, calling
 * it {@code guard} was not yet wrong — the word named the construct and every construct was one of
 * those. A comparison a behavior answers with stands in neither, so the word became a statement
 * about the rule that is false of it, and a document grouping by it puts rules of a body under a
 * construct they are not written in.
 *
 * <p>Held to the reader's word rather than to a spelling written down here. Both surfaces naming
 * {@code guard} would satisfy a pair of literals as readily as both naming the rule.
 */
class OneRuleIsCalledOneThingOnBothSurfacesTest {

    @Test
    void aDocumentCallsAComparisonWhatAReaderIsShown() {
        RuleRef.Comparison rule = new RuleRef.Comparison("f",
                new CoverageOrigin(new WrittenOwner.Body("m", "b"), 0, 0,
                        CoverageConstruct.IF));

        assertEquals(RuleCitation.WHAT_IT_IS, AdequacyReport.schemaRuleKind(rule));
    }
}
