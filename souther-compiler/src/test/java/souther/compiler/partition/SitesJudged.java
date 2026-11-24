package souther.compiler.partition;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;

/**
 * What {@link StopsOfABody} judges of each step of one behavior a run may stop at, each as the
 * walk of the body met it: the steps, in the order the walk first met each.
 *
 * <p>For a test that says which step a stop is shown at and at which value of the input: the
 * report words it for a reader, and the judgement is what it is worded from.
 */
final class SitesJudged {

    private SitesJudged() {}

    /** What is shown of every step of {@code behavior} in {@code compilation}'s one module. */
    static List<StopsOfABody.AtAStep> steps(Compilation compilation, String behavior) {
        String module = compilation.modules().getFirst();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value()
                .get(behavior);
        AnalysisBody analysis = checked.analysisBodies().get(behavior);
        InputReading read = inputs.reading(rules);
        return ComparisonReadings.of(behavior, analysis, read,
                InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                        inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                        inputs.dependencies()),
                ComparisonWitnesses.AtComparisons.NONE).stops().judged();
    }

    /** What is shown of every operation of every step of {@code behavior}, in the order the
     *  steps were met. */
    static List<StopAssessment.Judgement> of(Compilation compilation, String behavior) {
        return steps(compilation, behavior).stream()
                .flatMap(each -> each.operations().stream()).toList();
    }
}
