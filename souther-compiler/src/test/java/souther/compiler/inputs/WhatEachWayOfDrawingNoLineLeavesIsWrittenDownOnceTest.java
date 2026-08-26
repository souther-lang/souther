package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.CoverageObligation;
import souther.compiler.partition.ReportedReason;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every way a reading comes back without a line, and what each of them leaves behind, in one table.
 *
 * <p>The seal already refuses a reason nobody answered for: {@link BlockReason.RuleReadingStopped}
 * switches over its members with no {@code default}, so a fourteenth is a build failure. What it
 * does not refuse is a reason moved from one arm to another. Both switches keep compiling when a
 * reason changes which measure it leaves short or which word a document writes for it, and every
 * sentence built on the old answer goes on being written and is now wrong.
 *
 * <p>Which is not hypothetical here. Six of the nine rules below say both measures are short of
 * something and three say neither is, and that difference is what decides whether a behavior is
 * taken out of the verdict — a reason that quietly stopped leaving the border measure short would
 * let a model be called adequate over a rule this compiler never read. Issue #1079 is what that
 * costs when the answer is arrived at rather than written down.
 *
 * <p>So the answers are here, written out, and this is where they are changed. A reason that moves
 * fails this test and is meant to: what it is asking is not whether the code is right but whether
 * the person moving it meant to move it.
 */
class WhatEachWayOfDrawingNoLineLeavesIsWrittenDownOnceTest {

    /**
     * Every rule this compiler read and drew no line from, and what it leaves.
     *
     * <p>Written as {@code partition/boundary/word}: which of the two measures the rule leaves short
     * of something, and the word a document writes for it. A reason that leaves neither measure
     * short is one the model states rather than one this compiler fell short on.
     */
    private static Map<String, String> theRulesWithNoLine() {
        Map<String, String> table = new LinkedHashMap<>();
        // Read partway. What the rule would have divided or bounded is exactly the part that was
        // not read, so neither measure knows what it is missing and both are short.
        table.put("UnreadComparisonForm", "short/short/UNSUPPORTED_SYNTAX");
        table.put("UnreadComparisonDomain", "short/short/UNSUPPORTED_DOMAIN");
        table.put("RuleAboutADerivedValue", "short/short/RULE_ABOUT_A_DERIVED_VALUE");
        table.put("UnreadValueRule", "short/short/UNSUPPORTED_SYNTAX");
        // One word with `ComparisonBetweenPositions` below, and on purpose: they are the two
        // readings of `a < b`, opposite sentences about this compiler, and a document promises
        // its reader which kind of thing stopped a derivation rather than which reader stopped.
        table.put("ValueRuleRelatingTwoPositions", "short/short/UNSUPPORTED_PARTITION_SHAPE");
        table.put("CompetingCoordinates", "short/short/COMPETING_COORDINATES");
        // Read to the end. Whatever the rule places has been placed, and there is none to be owed.
        table.put("ComparisonCuttingNothing", "whole/whole/RULE_CUTS_NOTHING");
        table.put("ComparisonCuttingOutsideDomain",
                "whole/whole/RULE_CUTS_OUTSIDE_WHAT_THE_QUANTITY_HOLDS");
        table.put("ComparisonBetweenPositions", "whole/whole/UNSUPPORTED_PARTITION_SHAPE");
        return table;
    }

    /**
     * And every way the reading never got to a rule at all, which names a position and no rule.
     *
     * <p>Apart from the above because there is nothing to ask them: a reason with no rule behind it
     * has no {@code leavesShort} to answer, and the position it is about is short for both measures
     * by the position rather than by anything written about it.
     */
    private static Map<String, String> theStopsAtAPosition() {
        Map<String, String> table = new LinkedHashMap<>();
        table.put("TypeUnresolved", "TYPE_UNRESOLVED");
        table.put("DepthLimit", "DEPTH_LIMIT");
        table.put("UnsupportedTraversal", "UNSUPPORTED_TRAVERSAL");
        table.put("ValueRulesNotReached", "RULES_NOT_READ_AT_ALL");
        return table;
    }

    /**
     * The table, held against what the reasons answer.
     *
     * <p>Every member of the seal is here: the map is built from the reasons themselves, so one
     * added and left out of the table above comes back with no expectation beside it and fails.
     */
    @Test
    void everyRuleWithNoLineSaysWhatItLeavesAndWhatItIsCalled() {
        Map<String, String> said = new LinkedHashMap<>();
        for (BlockReason.RuleWithoutLineReason each : everyRuleWithoutALine()) {
            said.put(each.getClass().getSimpleName(),
                    (each.leavesShort(CoverageObligation.Measure.PARTITION) ? "short" : "whole")
                            + "/"
                            + (each.leavesShort(CoverageObligation.Measure.BOUNDARY)
                                    ? "short" : "whole")
                            + "/" + ReportedReason.of((BlockReason) each).name());
        }

        assertEquals(theRulesWithNoLine(), said);
    }

    /** The same of the reasons that name a position and no rule. */
    @Test
    void everyStopAtAPositionSaysWhatItIsCalled() {
        Map<String, String> said = new LinkedHashMap<>();
        for (BlockReason.AboutThePosition each : everyStopAtAPosition()) {
            said.put(each.getClass().getSimpleName(), ReportedReason.of(each).name());
        }

        assertEquals(theStopsAtAPosition(), said);
    }

    /**
     * Which half a reason is in decides both answers, and the table says the same thing.
     *
     * <p>The rule under the thirteen rows: a reading that stopped leaves whatever the rule states
     * unknown, so both measures are short of it; a rule read from end to end has had whatever it
     * places placed, so neither is. Said as a rule beside the rows, a reason added to the table with
     * the wrong pair of words fails here as well — the rows are what someone changing an answer has
     * to write, and this is what says whether the answer they wrote is one the halves allow.
     */
    @Test
    void aReadingThatStoppedLeavesBothShortAndOneThatFinishedLeavesNeither() {
        for (BlockReason.RuleWithoutLineReason each : everyRuleWithoutALine()) {
            boolean stopped = each instanceof BlockReason.RuleReadingStopped;
            assertEquals(stopped, each.leavesShort(CoverageObligation.Measure.PARTITION),
                    each.getClass().getSimpleName());
            assertEquals(stopped, each.leavesShort(CoverageObligation.Measure.BOUNDARY),
                    each.getClass().getSimpleName());
        }
    }

    /**
     * Every member of the seal, one of each.
     *
     * <p>Listed rather than found by reflection, because what this test is about is the answers and
     * a list that built itself from the same source would move with them. A member added is refused
     * by the switch in {@code leavesShort} before it reaches here, and one added and left out of the
     * table is what the assertions above catch.
     */
    private static List<BlockReason.RuleWithoutLineReason> everyRuleWithoutALine() {
        return List.of(
                new BlockReason.UnreadComparisonForm(),
                new BlockReason.UnreadComparisonDomain(),
                new BlockReason.RuleAboutADerivedValue(),
                new BlockReason.UnreadValueRule(),
                new BlockReason.ValueRuleRelatingTwoPositions(),
                new BlockReason.CompetingCoordinates(),
                new BlockReason.ComparisonCuttingNothing(),
                new BlockReason.ComparisonCuttingOutsideDomain(),
                new BlockReason.ComparisonBetweenPositions());
    }

    private static List<BlockReason.AboutThePosition> everyStopAtAPosition() {
        return List.of(
                new BlockReason.TypeUnresolved(),
                new BlockReason.DepthLimit(),
                new BlockReason.UnsupportedTraversal(BlockReason.Traversal.MAPPING_CONTENT),
                new BlockReason.ValueRulesNotReached());
    }
}
