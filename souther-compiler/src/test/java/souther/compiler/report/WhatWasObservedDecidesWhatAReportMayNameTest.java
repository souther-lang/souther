package souther.compiler.report;

import souther.compiler.query.WeakeningSet;
import souther.compiler.report.AdequacyReport;
import tools.jackson.databind.json.JsonMapper;
import tools.jackson.databind.node.ObjectNode;

import org.junit.jupiter.api.Test;

import souther.compiler.check.BehaviorImplementation;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.coverage.DecidedBy;
import souther.compiler.coverage.SourceOutcome;
import souther.compiler.diag.SourceNameResolver;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.query.Adequacy;
import souther.compiler.types.CoverageConstruct;
import souther.compiler.types.CoverageOrigin;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a report may name about the arms turns on what was observed, not on what the numbers came to.
 *
 * <p>Two questions and two answers. Whether every row could be read says whether an arm nothing was
 * seen to reach may still be reached; whether the numbers are a whole measure falls for that and for
 * a fork whose rule could not be worked out as well. Read as one, a build whose rows all ran is told
 * a row was not read, and every arm it certainly does not reach goes unsaid — which is the defect
 * the two were split apart over, arriving one layer later.
 */
class WhatWasObservedDecidesWhatAReportMayNameTest {

    private static final CoverageOrigin SETTLED =
            CoverageOrigin.written("m", 0, CoverageConstruct.IF);
    private static final CoverageOrigin UNSETTLED =
            CoverageOrigin.written("m", 1, CoverageConstruct.IF);

    private static CoverageSites.Site arm(CoverageOrigin fork, int index, DecidedBy decided) {
        return new CoverageSites.Site("b",
                new SourceOutcome.Held(new SourceOutcome.HeldBy.Condition()),
                souther.compiler.diag.Citation.of(new souther.compiler.diag.SourcePos(1, 1,
                        new souther.compiler.source.SourceId("0"))),
                index, index,
                new CoverageSites.Obligation("b", fork, index, decided));
    }

    /** Every row read, and one fork whose rule could not be worked out. */
    private static Adequacy.BranchEvidence read() {
        return Adequacy.BranchEvidence.measured("b",
                List.of(arm(SETTLED, 0, DecidedBy.THE_DECLARATION),
                        arm(SETTLED, 1, DecidedBy.THE_DECLARATION),
                        arm(UNSETTLED, 2, DecidedBy.NOT_SAID),
                        arm(UNSETTLED, 3, DecidedBy.NOT_SAID)),
                Set.of(0), souther.compiler.query.Adequacy.NOTHING_PROVEN, WeakeningSet.none());
    }

    /** The arm no row goes through is named, though the numbers are not a whole measure. */
    @Test
    void theArmNoRowGoesThroughIsStillNamed() {
        ObjectNode behavior = JsonMapper.builder().build().createObjectNode();
        AdequacyReport.branch(behavior, read(),
                new DocumentSources(SourceNameResolver.identity()));

        assertEquals(1, behavior.get("branch").get("unreached").size(),
                () -> "the settled fork's other arm: " + behavior.get("branch"));
        assertEquals("partial", behavior.get("branch").get("status").asString(),
                "and the numbers still say they are not a whole measure");
    }

    /** And nothing says a row was not read, because every one was. */
    @Test
    void andNothingSaysARowWasNotRead() {
        StringBuilder out = new StringBuilder();
        new AdequacyReport(AdequacyReport.SCHEMA_VERSION, "x",
                souther.compiler.query.Adequacy.Asked.fullReport(), WeakeningSet.none(),
                List.of()).branch(out,
                new AdequacyReport.BehaviorReport("b", BehaviorImplementation.IMPLEMENTED, 1, 0,
                        WeakeningSet.none(), null, null, null, read(), List.of()),
                null, SourceNameResolver.identity());

        assertTrue(out.toString().contains("branch      1/4"),
                () -> "what the arms came to: " + out);
        assertFalse(out.toString().contains("a row was not read"),
                () -> "every row was read: " + out);
    }
}
