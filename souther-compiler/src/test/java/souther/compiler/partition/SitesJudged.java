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

import java.util.ArrayList;
import java.util.List;

/**
 * What {@link StopAssessment} judges of each place a run may stop in each comparison of one
 * behavior, asked of every place the comparison is worked out at with a row arriving, along the
 * way the comparison stands on.
 *
 * <p>For a test that says which site a stop is shown at and at which value of the input: the
 * report words it for a reader, and the judgement is what it is worded from.
 */
final class SitesJudged {

    private SitesJudged() {}

    /** The judgements of every comparison of {@code behavior} in {@code compilation}'s one
     *  module, in the order the comparisons are read. */
    static List<StopAssessment.Judgement> of(Compilation compilation, String behavior) {
        String module = compilation.modules().getFirst();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value()
                .get(behavior);
        AnalysisBody analysis = checked.analysisBodies().get(behavior);
        InputReading read = inputs.reading(rules);
        List<StopAssessment.Judgement> out = new ArrayList<>();
        for (ComparisonReadings.Reading each : ComparisonReadings.of(behavior, analysis, read,
                InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                        inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                        inputs.dependencies()),
                ComparisonWitnesses.AtComparisons.NONE).comparisons()) {
            List<StopAssessment.Place> places = new ArrayList<>();
            for (ComparisonReadings.Reading.WorkedOutAt worked : each.whatARunWorksOut()) {
                places.add(new StopAssessment.Place(worked, true, each.assumed()));
            }
            out.addAll(StopAssessment.of(each, places, false, read));
        }
        return out;
    }
}
