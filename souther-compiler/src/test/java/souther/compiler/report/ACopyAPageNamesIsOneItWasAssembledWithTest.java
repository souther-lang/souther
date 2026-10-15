package souther.compiler.report;

import org.junit.jupiter.api.Test;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.partition.ConditionGap;
import souther.compiler.partition.ConditionOccurrence;
import souther.compiler.partition.ConditionReportAnchor;
import souther.compiler.partition.OnTheWay;
import souther.compiler.partition.ReachabilityGap;
import souther.compiler.partition.SaidOnTheWay;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrences;
import souther.compiler.types.ExpansionSite;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.StepOfACopy;
import souther.compiler.types.ValueName;
import souther.compiler.types.WrittenOwner;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A copy of a helper's code a page names is one the page was assembled with, and a copy it was
 * not is raised rather than shown naming no call.
 *
 * <p>Where each call is written is read off the compilation when the page is assembled, gathered
 * off everything the page may name a copy of. A holder of copies the gathering missed would
 * otherwise come out as a gap naming no call — which reads as a condition of the body itself.
 */
class ACopyAPageNamesIsOneItWasAssembledWithTest {

    private static final ModelOccurrence IN_THE_CALL = new ModelOccurrence(
            SourceConstructOrigin.written(new WrittenOwner.Body("m", "positive"), 1,
                    SourceConstruct.BINARY),
            ExpansionLineage.ORIGINAL.copiedInto(new ValueName.Helper("m", "positive"),
                    new ExpansionSite.Written(SourceConstructOrigin.written(
                            new WrittenOwner.Body("m", "f"), 1, SourceConstruct.CALL))));

    private static final OnTheWay.Declined DECLINED = new OnTheWay.Declined(
            new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, 0),
            new ConditionReportAnchor.WhereTheReadingMetIt("m",
                    new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, 0)),
            new WhyNotTaken.OutsideDomain(WhyNotTaken.DomainLimit.A_QUANTITY_ON_NO_ORDER));

    private static final ConditionGap GAP =
            new ConditionGap.OfTheInput(new ReachabilityGap.Unstated(DECLINED));

    private static final SaidOnTheWay WAY =
            new SaidOnTheWay(Map.of(DECLINED, ModelOccurrences.of(IN_THE_CALL)), Map.of(),
                    Map.of());

    @Test
    void aCopyThePageWasAssembledWithNamesItsCalls() {
        AdequacyReport.CopyShown copy = new AdequacyReport.CopyShown(null,
                List.of(new AdequacyReport.CallSite(
                        StepOfACopy.of(IN_THE_CALL.lineage()).getFirst(), "positive", null)));
        AdequacyReport.ConditionsShown shown = new AdequacyReport.ConditionsShown(Map.of(),
                Map.of(IN_THE_CALL, copy), WAY);
        assertEquals(List.of(copy), shown.copiesOf(GAP),
                "the gap names the call its copy was made at");
    }

    @Test
    void aCopyItWasNotAssembledWithIsRaised() {
        AdequacyReport.ConditionsShown shown =
                new AdequacyReport.ConditionsShown(Map.of(), Map.of(), WAY);
        assertThrows(IllegalStateException.class, () -> shown.copiesOf(GAP),
                "a copy the gathering missed is raised, not shown naming no call");
    }
}
