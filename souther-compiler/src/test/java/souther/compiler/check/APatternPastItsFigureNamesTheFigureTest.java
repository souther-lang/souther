package souther.compiler.check;

import net.unit8.notation199x.pattern.Meter;
import org.junit.jupiter.api.Test;

import souther.compiler.inputs.BlockReason;
import souther.compiler.observe.Figure;
import souther.compiler.observe.RunSensitivity;
import souther.compiler.observe.WorkFigure;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.regex.PatternPlan;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.values.StoppedReading;
import souther.compiler.values.UnreadReason;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A stop that a wider run could get past names the figure it stopped at, and the figure is the one
 * the run was held to.
 *
 * <p>Two claims. The first is over the reasons: a reason a run allowed more may get past names a
 * figure, so a report told the one is never without the other — and the converse is not claimed,
 * because a reason can reach a figure and be held by something else as well. The second is over a
 * reading: the figure a pattern was refused at is carried from where the machine was refused, so a
 * run handed another budget names that budget's number and not one written down somewhere else.
 */
class APatternPastItsFigureNamesTheFigureTest {

    private static final Figure AT_A_FIGURE = WorkFigure.ADMITTED_VALUES_ONE_MACHINE.at(300);

    /** A reason a wider run may get past names the figure it stopped at. */
    @Test
    void aReasonAWiderRunMayGetPastNamesAFigure() {
        List<String> unnamed = new ArrayList<>();
        for (BlockReason.ReadingStopReason each : everyStop()) {
            if (each.runSensitivity() == RunSensitivity.MAY_CHANGE && each.figures().isEmpty()) {
                unnamed.add(each.toString());
            }
        }

        assertEquals(List.of(), unnamed,
                "a reason a wider run may get past names what it stopped at");
    }

    /**
     * And a reason that reached a figure names it however else it was stopped.
     *
     * <p>Sets a position could not hand on because its own answer stopped at a figure and at a form
     * nothing reads: a run allowed more meets the form again, and the figure was reached all the
     * same. Named only where a wider run gets past, a reader would be told nothing was reached.
     */
    @Test
    void aReasonStoppedAtAFigureAndAtSomethingElseNamesTheFigureAndGetsNoWiderRunPastIt() {
        BlockReason.RulesNotHandedOnAsSets both =
                new BlockReason.RulesNotHandedOnAsSets(List.of(AT_A_FIGURE), true);

        assertEquals(RunSensitivity.UNAFFECTED, both.runSensitivity());
        assertEquals(List.of(AT_A_FIGURE), both.figures());
    }

    /** Each figure that is fixed where it is declared is the one said. */
    @Test
    void aFigureFixedWhereItIsDeclaredIsTheOneSaid() {
        assertEquals(List.of(CompositionBudget.READINGS_OF_ONE_CONDITION.figure()),
                new BlockReason.WhatItStatesIsNoLine(
                        BlockReason.WhatItStatesIsNoLine.Why.MORE_READINGS_THAN_ARE_MADE).figures());
        assertEquals(List.of(WorkFigure.ELEMENTS_A_WALK_WRITES_OUT.at(
                        ElementsWrittenOut.MOST_WALKED)),
                new BlockReason.WhatItStatesIsNoLine(
                        BlockReason.WhatItStatesIsNoLine.Why.MORE_ELEMENTS_THAN_ARE_WRITTEN_OUT)
                        .figures());
        assertEquals(List.of(WorkFigure.FIELDS_A_RULE_IS_FOLLOWED_DOWN.at(
                        GuaranteeWalk.FIELDS_SEEDED)),
                new BlockReason.ValueRulesNotReachedPastDepthLimit().figures());
        assertEquals(List.of(WorkFigure.ORDERED_EXTENT_ONE_MACHINE.at(
                        PatternPlan.Budget.OF_AN_ORDERED_EXTENT.mostStates() + " states or "
                                + PatternPlan.Budget.OF_AN_ORDERED_EXTENT.mostWork()
                                + " looked at")),
                new BlockReason.OrderedExtentTooCostly(Meter.Stopped.ONE_MACHINE).figures());
        PatternPlan.Budget extent = PatternPlan.Budget.OF_AN_ORDERED_EXTENT;
        assertEquals(List.of(WorkFigure.ORDERED_EXTENT_IN_ALL.at(extent.mostBuilt()
                        + " states built and " + extent.mostWork() + " looked at")),
                new BlockReason.OrderedExtentTooCostly(Meter.Stopped.THE_ANSWER).figures());
    }

    /**
     * And a figure an allowance is handed by a run is the number that run used.
     *
     * <p>Two runs of one model under two budgets, each too small for the pattern's machine: each
     * names the budget it was handed. A figure written down beside the reason, and not carried
     * from where the machine was refused, would come out the same both times.
     */
    @Test
    void aPatternRefusedUnderABudgetARunWasHandedNamesThatBudget() {
        assertEquals(new BlockReason.PatternTooCostly(WorkFigure.ADMITTED_VALUES_ONE_MACHINE
                        .at("100 states or 1000000000 looked at")),
                whatStoppedTheReading(new PatternPlan.Budget(100, 1_000_000, 1_000_000_000L)));
        assertEquals(new BlockReason.PatternTooCostly(WorkFigure.ADMITTED_VALUES_ONE_MACHINE
                        .at("200 states or 1000000000 looked at")),
                whatStoppedTheReading(new PatternPlan.Budget(200, 1_000_000, 1_000_000_000L)));
    }

    /**
     * And where the machine fits one machine and the answer had already built what it may, the
     * answer is what was refused, at what it may build in all.
     */
    @Test
    void anAnswerRefusedForWhatItBuiltInAllNamesThatFigure() {
        PatternPlan.Budget small = new PatternPlan.Budget(1_000_000, 100, 1_000_000_000L);

        assertEquals(new BlockReason.ExactValuesTooCostly(WorkFigure.ADMITTED_VALUES_IN_ALL.at(
                        "100 states built and 1000000000 looked at")),
                whatStoppedTheReading(small));
    }

    /** One of each stop there is that carries what it stopped at, and the rest of the stops. */
    private static List<BlockReason.ReadingStopReason> everyStop() {
        List<BlockReason.ReadingStopReason> out = new ArrayList<>(List.of(
                new BlockReason.PatternTooCostly(AT_A_FIGURE),
                new BlockReason.ExactValuesTooCostly(AT_A_FIGURE),
                new BlockReason.BehaviorDistinctionsTooCostly(
                        WorkFigure.BEHAVIOR_DISTINCTIONS_ONE_MACHINE.at(300)),
                new BlockReason.RulesNotHandedOnAsSets(List.of(
                        WorkFigure.RULE_SETS_ONE_MACHINE.at(300)), false),
                // A position whose own answer stopped at a form nothing reads handed nothing on,
                // and no figure is why.
                new BlockReason.RulesNotHandedOnAsSets(List.of(), true),
                // And one whose answer stopped at both: the figure is reached, and a run allowed
                // more meets the form again.
                new BlockReason.RulesNotHandedOnAsSets(List.of(
                        WorkFigure.ADMITTED_VALUES_ONE_MACHINE.at(300)), true),
                new BlockReason.OrderedExtentTooCostly(Meter.Stopped.ONE_MACHINE),
                new BlockReason.OrderedExtentTooCostly(Meter.Stopped.THE_ANSWER),
                new BlockReason.ValueRulesNotReachedPastDepthLimit(),
                new BlockReason.ValueRulesNotReached(),
                new BlockReason.TypeUnresolved(),
                new BlockReason.UnreadComparisonForm(),
                new BlockReason.UnreadComparisonDomain(),
                new BlockReason.LineAtANumberNoRatioHolds(),
                new BlockReason.LineSideNotWorkedOut(
                        souther.compiler.numeric.UnheldNumber.NO_REPRESENTATION_EXISTS),
                new BlockReason.RuleAboutADerivedValue(),
                new BlockReason.RuleAboutAnElementOfSeveralContainers(),
                new BlockReason.UnreadValueRule(),
                new BlockReason.NonAffineArithmetic(
                        NonAffineOperation.PRODUCT_OF_NON_CONSTANT_VALUES),
                new BlockReason.EndLeftOpenByAChoice(),
                new BlockReason.ValueRuleLeftOpenByAChoice(),
                new BlockReason.ValueRuleRelatingTwoPositions(),
                new BlockReason.ValueRuleRelatingElements(),
                new BlockReason.CasePairingNotDetermined(),
                new BlockReason.SeveralLinesInOneRule(),
                new BlockReason.RelationNotShownToReachEveryValue()));
        for (BlockReason.WhatItStatesIsNoLine.Why why
                : BlockReason.WhatItStatesIsNoLine.Why.values()) {
            out.add(new BlockReason.WhatItStatesIsNoLine(why));
        }
        // And what a value reading's own account comes to, every reason of it.
        for (UnreadReason why : UnreadReason.values()) {
            out.add(BlockReason.of(StoppedReading.carriesAFigure(why)
                    ? new StoppedReading(why, AT_A_FIGURE) : StoppedReading.of(why)));
        }
        return out;
    }

    /**
     * What stopped the reading of the one position of a declaration whose rule is a pattern of
     * three hundred characters, under {@code admitted} as what a position's values may cost.
     */
    private static BlockReason.ReadingStopReason whatStoppedTheReading(
            PatternPlan.Budget admitted) {
        Compilation compilation = Compilation.ofSource("""
                module demo

                data Long = String
                    invariant plain = String.matches("a{300}", value)
                    invariant marked = String.matches("a{300}b?", value)
                """, "Main");
        compilation.answerEverything();
        Symbols symbols = Scopes.derived(compilation.db(), "demo").value();
        TypeSymbol.AtModule name = TypeSymbols.declared(new TypeKey(symbols.module(), "Long"));
        ReadingPolicy policy = new ReadingPolicy(ReadAs.THE_COMPILATION_DOES.dnfExpansionLimit(),
                ReadAs.THE_COMPILATION_DOES.scalePlacesLimit(), admitted,
                PatternPlan.Budget.OF_WHAT_A_RULE_LEAVES);
        FieldDomains read = FieldDomains.of(name,
                RuleReadingContext.unshared(RuleReadings.of(compilation, "demo"), policy));
        StoppedReading stopped = read.admits(RuleKey.THE_VALUE).whyPartial();
        assertNotNull(stopped, "a reading refused a machine is short of the rules it was about");
        return assertInstanceOf(BlockReason.ReadingStopReason.class, BlockReason.of(stopped));
    }
}
