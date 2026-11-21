package souther.compiler.partition;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.diag.Citation;
import souther.compiler.diag.PhysicalPos;
import souther.compiler.diag.SourceRendering;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

/**
 * What is judged of each construction on the way to each rule of one behavior
 * ({@link ConstructionStopAssessment}), by the line the construction is written on: the kinds of
 * judgement it was given, of every rule it is on the way to.
 *
 * <p>For a test that says a construction stops no run. The report says nothing of one, and says
 * the same of one never asked about, so the judgement is what tells the two apart.
 */
final class ConstructionsJudged {

    private ConstructionsJudged() {}

    /** The kinds of judgement each construction of {@code behavior} in {@code compilation}'s one
     *  module was given, by its line. */
    static Map<Integer, Set<String>> of(Compilation compilation, String behavior) {
        Map<Integer, Set<String>> out = new TreeMap<>();
        byRule(compilation, behavior).values().forEach(rule -> rule.forEach((line, kinds) ->
                out.computeIfAbsent(line, _ -> new TreeSet<>()).addAll(kinds)));
        return out;
    }

    /** The same, rule by rule: by the line and column each rule of {@code behavior} is written
     *  at, the kinds of judgement each construction on the way to it was given, by its line. */
    static Map<String, Map<Integer, Set<String>>> byRule(Compilation compilation,
                                                        String behavior) {
        String module = compilation.modules().getFirst();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value()
                .get(behavior);
        AnalysisBody analysis = checked.analysisBodies().get(behavior);
        InputReading read = inputs.reading(rules);
        SourceRendering rendering = SourceRendering.namedByIdentity(compilation.texts());
        Map<String, Map<Integer, Set<String>>> out = new TreeMap<>();
        for (ComparisonReadings.Reading each : ComparisonReadings.of(behavior, analysis, read,
                InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                        inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                        inputs.dependencies()),
                ComparisonWitnesses.AtComparisons.NONE).comparisons()) {
            Reachability way = Reachability.of(new WayToTheBorder(each.assumed()),
                    read.quantities().region());
            if (!(each.at() instanceof Citation.Written written)) {
                continue;
            }
            PhysicalPos rule = rendering.layouts().resolve(written.at());
            Map<Integer, Set<String>> ofTheRule = out.computeIfAbsent(
                    rule.line() + ":" + rule.column(), _ -> new TreeMap<>());
            for (ConstructionStopAssessment.Judgement judged : ConstructionStopAssessment.of(each,
                    way instanceof Reachability.Reaching reaching ? List.of(reaching.region())
                            : List.of(), read)) {
                ofTheRule.computeIfAbsent(rendering.layouts().resolve(judged.made().pos()).line(),
                        _ -> new TreeSet<>()).add(judged.getClass().getSimpleName());
            }
        }
        return out;
    }
}
