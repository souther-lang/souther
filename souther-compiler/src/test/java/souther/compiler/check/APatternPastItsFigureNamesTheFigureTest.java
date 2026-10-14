package souther.compiler.check;

import net.unit8.notation199x.pattern.Meter;
import org.junit.jupiter.api.Test;

import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.WrittenOutElements;
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
 * <p>Two claims. The first is over the reasons: a reason says a figure exactly where it says a run
 * allowed more may get past it, so a report told one is never without the other. The second is
 * over a reading: the figure a pattern was refused at is carried from where the machine was
 * refused, so a run handed another budget names that budget's number and not one written down
 * somewhere else.
 */
class APatternPastItsFigureNamesTheFigureTest {

    private static final Figure AT_A_FIGURE = WorkFigure.ADMITTED_VALUES_ONE_MACHINE.at(300);

    /** A reason names a figure exactly where a wider run may get past it. */
    @Test
    void aReasonNamesAFigureExactlyWhereAWiderRunMayGetPastIt() {
        List<String> disagreeing = new ArrayList<>();
        for (BlockReason.ReadingStopReason each : everyStop()) {
            boolean mayChange = each.runSensitivity() == RunSensitivity.MAY_CHANGE;
            if (mayChange == each.figures().isEmpty()) {
                disagreeing.add(each + " " + each.runSensitivity() + " " + each.figures());
            }
        }

        assertEquals(List.of(), disagreeing,
                "a reason a wider run may get past names what it stopped at, and one it cannot"
                        + " names nothing");
    }

    /** Each figure that is fixed where it is declared is the one said. */
    @Test
    void aFigureFixedWhereItIsDeclaredIsTheOneSaid() {
        assertEquals(List.of(CompositionBudget.READINGS_OF_ONE_CONDITION.figure()),
                new BlockReason.WhatItStatesIsNoLine(
                        BlockReason.WhatItStatesIsNoLine.Why.MORE_READINGS_THAN_ARE_MADE).figures());
        assertEquals(List.of(WorkFigure.ELEMENTS_A_WALK_WRITES_OUT.at(
                        WrittenOutElements.MOST_WALKED)),
                new BlockReason.WhatItStatesIsNoLine(
                        BlockReason.WhatItStatesIsNoLine.Why.MORE_ELEMENTS_THAN_ARE_WRITTEN_OUT)
                        .figures());
        assertEquals(List.of(WorkFigure.FIELDS_A_RULE_IS_FOLLOWED_DOWN.at(
                        GuaranteeWalk.FIELDS_SEEDED)),
                new BlockReason.ValueRulesNotReachedPastDepthLimit().figures());
        assertEquals(List.of(WorkFigure.ORDERED_EXTENT_ONE_MACHINE.at(
                        PatternPlan.Budget.OF_AN_ORDERED_EXTENT.mostStates())),
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
        assertEquals(new BlockReason.PatternTooCostly(
                        WorkFigure.ADMITTED_VALUES_ONE_MACHINE.at(100)),
                whatStoppedTheReading(new PatternPlan.Budget(100, 1_000_000, 1_000_000_000L)));
        assertEquals(new BlockReason.PatternTooCostly(
                        WorkFigure.ADMITTED_VALUES_ONE_MACHINE.at(200)),
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
                        WorkFigure.RULE_SETS_ONE_MACHINE.at(300))),
                // A position whose own answer stopped at a form nothing reads handed nothing on,
                // and no figure is why.
                new BlockReason.RulesNotHandedOnAsSets(List.of()),
                new BlockReason.OrderedExtentTooCostly(Meter.Stopped.ONE_MACHINE),
                new BlockReason.OrderedExtentTooCostly(Meter.Stopped.THE_ANSWER),
                new BlockReason.ValueRulesNotReachedPastDepthLimit(),
                new BlockReason.ValueRulesNotReached(),
                new BlockReason.TypeUnresolved(),
                new BlockReason.RecursiveExpansion(TypeSymbols.declared(new TypeKey("g", "Chain")),
                        TermPath.of("c")),
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
            out.add(BlockReason.of(new StoppedReading(why,
                    StoppedReading.carriesAFigure(why) ? AT_A_FIGURE : null)));
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
