package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.regex.PatternPlan;
import souther.compiler.values.Allowance;
import souther.compiler.values.Value;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a behavior's rules about the strings at a position divide it into, and what is said about the
 * ones that divide it into nothing.
 *
 * <p>The crossing from a rule to the values on either side of it. What comes out is two sets, both
 * built here and neither derived from the other by whoever holds them — so a reader downstream never
 * complements a language under an allowance of its own, and "the values it admits are known and the
 * rest are not" is a state with no spelling.
 *
 * <p><b>The position is the unit.</b> Two rules about one position are two distinctions of one
 * denominator, and a reader told about one of them is told about a partition the model does not
 * draw. So the rules of a position are built as one group, and a group that cannot be built leaves
 * the position divided by none of them.
 *
 * <p>And every rule that reaches here is answered for. The ones that divide come back as divisions
 * and the ones that do not come back as what became of them, which is what keeps a rule from
 * leaving without a sentence about it.
 */
class WhatABehaviorsRuleAboutItsStringsDividesAPositionIntoTest {

    @Test
    void aRuleAboutTheStringsDividesThePositionIntoWhatItAdmitsAndTheRest() {
        SetDivisions.Read read = readingsOf("""
                behavior f : (code: String) -> Answer
                let f (code) = if String.startsWith("JP", code) then Yes else No
                """);

        assertEquals(List.of(), read.blocked(), "the rule divides the position");
        SetDivision only = divisionIn(read);
        assertEquals(new NumericTerm.ValueOf(souther.compiler.inputs.TermPath.of("code")),
                only.term(), "the position the rule is written about");
        assertTrue(only.whenTrue().has(new Value.Text("JP-1")),
                "a string that satisfies the rule is on the side that does");
        assertFalse(only.whenFalse().has(new Value.Text("JP-1")),
                "and on no other");
        assertTrue(only.whenFalse().has(new Value.Text("US-1")),
                "and one that does not is on the side that does not");
        assertFalse(only.whenTrue().has(new Value.Text("US-1")),
                "and on no other");
    }

    /**
     * Two rules about one position are two divisions of it, built together.
     *
     * <p>Not two answers about one thing: the position is divided by both, and a reader given one of
     * them holds a partition the model does not draw.
     */
    @Test
    void twoRulesAboutOnePositionAreTwoDivisionsOfIt() {
        SetDivisions.Read read = readingsOf("""
                behavior f : (code: String) -> Answer
                let f (code) =
                    if String.startsWith("JP", code) then Yes
                    else if String.endsWith("X", code) then Yes else No
                """);

        assertEquals(List.of(), read.blocked(), "both rules divide the position");
        assertEquals(2, read.divided().size(), "and each of them is a division of it");
        assertEquals(1, read.divided().stream().map(PartitionEvidence::at).distinct().count(),
                "of the one position both are written about");
    }

    /**
     * A rule every value satisfies divides nothing, and is said to.
     *
     * <p>Every string begins with the empty one, so one side of this holds every string and the
     * other holds none. What that comes to at the position is not this stage's answer: what a rule
     * leaves is a set of every string there is, and what the position holds is what its
     * declarations left it — so a side empty among the strings and a side empty at the position are
     * two facts, and only the second says the position is undivided.
     *
     * <p>So the rule is read and handed on, and nothing here is held open by it. Judged here, this
     * stage would be deciding a position's classes out of the strings, which is the authority it
     * does not have.
     */
    @Test
    void aRuleEveryStringSatisfiesIsStillHandedOn() {
        SetDivisions.Read read = readingsOf("""
                behavior f : (code: String) -> Answer
                let f (code) = if String.startsWith("", code) then Yes else No
                """);

        assertEquals(1, read.divided().size(), "the rule is read and handed on");
        assertEquals(List.of(), read.blocked(),
                "and nothing about the position's classes is held open by it");
    }

    /**
     * A rule about a value made from the position divides no position.
     *
     * <p>What it states is true of something the position was turned into, and there is no
     * denominator for it to divide: a class of the values here cannot be read off a class of what an
     * operation made from them.
     *
     * <p><b>And nothing is filed, because nothing places it.</b> A finding is shown at a position,
     * and the value this rule is about came from none that the reading can name — an operation
     * standing between the rule and the position is exactly what the reading has no path through. So
     * the rule is read, it divides nothing, and there is nowhere to say so.
     *
     * <p>Which is what the reading of a comparison does with the same shape
     * ({@link ComparisonAssessment}), and it is a limitation the two share rather than one of this
     * walk. Pinned here so that it is a fact somebody wrote down: an author writing this rule is
     * told nothing about it.
     */
    @Test
    void aRuleAboutAValueMadeFromThePositionDividesNoPosition() {
        SetDivisions.Read read = readingsOf("""
                behavior f : (code: String) -> Answer
                let f (code) = if String.startsWith("JP", String.trim(code)) then Yes else No
                """);

        assertEquals(List.of(), read.divided(), "no position is divided");
        assertEquals(List.of(), read.blocked(),
                "and nothing is filed, because the value it is about came from no position the"
                        + " reading can name");
    }

    /**
     * A position whose group cannot be built is divided by none of its rules.
     *
     * <p>The whole of why the position is the unit, shown with an allowance that affords neither.
     * Built one at a time, which of the two a reader heard about would follow the order the body
     * happened to be walked in — and the answer would be a partition of the position that the model
     * does not draw, rather than the position undivided.
     */
    @Test
    void aPositionWhoseGroupCannotBeBuiltIsDividedByNoneOfItsRules() {
        SetDivisions.Read read = readingsOf("""
                behavior f : (code: String) -> Answer
                let f (code) =
                    if String.startsWith("JP", code) then Yes
                    else if String.endsWith("X", code) then Yes else No
                """,
                // One state is fewer than the smallest of these rules needs, so the group is
                // refused where reading each of them was fine.
                new PatternPlan.Budget(1, 1));

        assertEquals(List.of(), read.divided(), "neither rule divides the position");
        assertEquals(List.of(new BlockReason.BehaviorDistinctionsTooCostly(),
                        new BlockReason.BehaviorDistinctionsTooCostly()),
                read.blocked().stream().map(ClassingBlocker::why).toList(),
                "and both are answered for as the position's distinctions not being built");
    }

    /** The one division the model under test states. */
    private static SetDivision divisionIn(SetDivisions.Read read) {
        assertEquals(1, read.divided().size(), "the model under test states one division");
        return ((PartitionEvidence.BySet) read.divided().get(0)).division();
    }

    private static SetDivisions.Read readingsOf(String behavior) {
        return readingsOf(behavior, PatternPlan.Budget.OF_BEHAVIOR_DISTINCTIONS);
    }

    /** What {@code behavior}'s rules about its strings divide, built under {@code budget}. */
    private static SetDivisions.Read readingsOf(String behavior, PatternPlan.Budget budget) {
        String source = """
                module demo

                data Yes
                data No
                data Answer = Yes | No

                """ + behavior;
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(each -> each.diagnostic().code() + " " + each.diagnostic().primary())
                        .toList(),
                "the model under test compiles");
        String module = compilation.modules().get(0);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        AnalysisBody body = checked.analysisBodies().get("f");
        assertNotNull(body, "the behavior has a body for the analysis to read");
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value().get("f");
        PredicateReadings read = PredicateReadings.of("f", body, inputs.reading(rules),
                inputs.parameterReads(), checked.elementBindings().get("f"));
        Allowance<NumericTerm.FromOnePosition> allowance = Allowance.of(budget);
        return SetDivisions.of(read, rules.symbols(), allowance);
    }
}
