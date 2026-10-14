package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.test.Nightly;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The decision of a chain of helper calls long enough to have more ways through it than a decision
 * is read for is read to that figure and says it stopped there, and comes to an end.
 *
 * <p>A helper called on what the last call answered splits the ways at every call, so the ways
 * double with the chain; most pairings of them are ways no run takes, refused where they are
 * joined. What bounds the reading is the figure, and this holds the chain to reaching it rather
 * than to some number of seconds.
 *
 * <p>Asked once a night. Reaching the figure is reading as many ways as it lets through, which
 * takes seconds however the joining is done. That a reading stops at the figure and says so is held
 * on every change by
 * {@code AWeakeningAWiderRunMayAnswerNamesTheFigureThatStoppedItTest} on a body small enough to
 * read in a moment; a chain of calls coming to the figure by another route is found by the morning.
 */
@Nightly
class ACaseChainPastTheWaysADecisionIsReadForStopsThereTest {

    @Test
    void theDecisionStopsAtTheWaysItIsReadForAndSaysSo() {
        int calls = 32 - Integer.numberOfLeadingZeros(
                CompositionBudget.PATHS_OF_A_DECISION_READ.maximum());
        Compilation compilation = Compilation.ofSource(
                ACaseChainIsReadNoFurtherInAllThanOneConditionIsReadTest.model(calls), "Main");
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("demo")).value();
        assertNotNull(checked, "the chain under test compiles");
        AnalysisBody analysis = checked.analysisBodies().get("draw");
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("demo")).value().get("draw");
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());

        DecisionReading decision = DecisionReading.of("draw", analysis, inputs.reading(rules),
                reads);

        assertEquals(new DecisionReading.Enumeration.StoppedAtAFigure(
                CompositionBudget.PATHS_OF_A_DECISION_READ), decision.enumeration());
        assertTrue(decision.found().size()
                <= CompositionBudget.PATHS_OF_A_DECISION_READ.maximum());
    }
}
