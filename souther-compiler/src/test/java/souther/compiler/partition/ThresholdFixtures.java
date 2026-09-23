package souther.compiler.partition;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.PathReachability;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.StatedContract;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.RulesWithNoLine;
import souther.compiler.values.Allowance;

import java.util.ArrayList;
import java.util.List;

/**
 * Ways a test with no measurement pipeline beside it reads thresholds or assembles a partition on
 * its own.
 *
 * <p>Each of these is a caller supplying a default or an assembled parameter and delegating whole
 * to the one production computation — {@link GuardThresholds#of(String, AnalysisBody, Core,
 * CoverageSites.Plan, InputDomain, RuleReadingContext, PathReachability.Answers,
 * RuleReachNumbering)}, {@link EnsuresThresholds#of(StatedContract, souther.compiler.inputs.InputReading)}
 * and {@link Partitions#withEvidence}. None of these fixtures reads a comparison or a clause a
 * second way; they only fill in what a caller with a narrower question does not need to say.
 */
final class ThresholdFixtures {

    /**
     * The thresholds one behavior's body compares its parameters against, read against no known
     * reachability.
     */
    static GuardThresholds.Guards guardsOf(String behavior, AnalysisBody states, Core emitted,
                                           CoverageSites.Plan plan,
                                           InputDomain inputs, RuleReadingSource source) {
        return states == null ? GuardThresholds.Guards.NONE
                : GuardThresholds.of(behavior, states, emitted, plan, inputs.reading(source),
                        ElementBindings.of(states, source.newtypes()),
                        PathReachability.Answers.NONE,
                        new RuleReachNumbering(source.symbols().module(), behavior));
    }

    /** The lines one behavior's clauses draw, reading the input's rules here. */
    static EnsuresThresholds.Clauses clausesOf(StatedContract stated, InputDomain inputs,
                                               RuleReadingSource source) {
        return EnsuresThresholds.of(stated, inputs.reading(source));
    }

    static Partitions.Partitioning withThresholds(Partitions.Partitioning base,
                                                   Quantities reading,
                                                   List<Threshold> thresholds,
                                                   RuleReadingContext ruleReading,
                                                   Allowance<NumericTerm.FromOnePosition> allowance) {
        return withThresholds(base, reading, thresholds, ruleReading, RulesWithNoLine.NONE,
                allowance);
    }

    static Partitions.Partitioning withThresholds(Partitions.Partitioning base,
                                                   Quantities reading,
                                                   List<Threshold> thresholds,
                                                   RuleReadingContext ruleReading,
                                                   RulesWithNoLine rulesWithoutALine,
                                                   Allowance<NumericTerm.FromOnePosition> allowance) {
        return withThresholds(base, reading, thresholds, ruleReading, rulesWithoutALine,
                List.of(), allowance);
    }

    static Partitions.Partitioning withThresholds(Partitions.Partitioning base,
                                                   Quantities reading,
                                                   List<Threshold> thresholds,
                                                   RuleReadingContext ruleReading,
                                                   RulesWithNoLine rulesWithoutALine,
                                                   List<GuardThresholds.Guards.Singled> singled,
                                                   Allowance<NumericTerm.FromOnePosition> allowance) {
        return withThresholds(base, reading, thresholds, ruleReading, rulesWithoutALine,
                singled, List.of(), allowance);
    }

    static Partitions.Partitioning withThresholds(Partitions.Partitioning base,
                                                   Quantities reading,
                                                   List<Threshold> thresholds,
                                                   RuleReadingContext ruleReading,
                                                   RulesWithNoLine rulesWithoutALine,
                                                   List<GuardThresholds.Guards.Singled> singled,
                                                   List<LineDrawn> between,
                                                   Allowance<NumericTerm.FromOnePosition> allowance) {
        return withThresholds(base, reading, thresholds, ruleReading, rulesWithoutALine,
                singled, between, ReachingCuts.NONE, allowance);
    }

    static Partitions.Partitioning withThresholds(Partitions.Partitioning base,
                                                   Quantities reading,
                                                   List<Threshold> thresholds,
                                                   RuleReadingContext ruleReading,
                                                   RulesWithNoLine rulesWithoutALine,
                                                   List<GuardThresholds.Guards.Singled> singled,
                                                   List<LineDrawn> between,
                                                   ReachingCuts reaching,
                                                   Allowance<NumericTerm.FromOnePosition> allowance) {
        List<RuleEvidence> evidence = new ArrayList<>();
        thresholds.forEach(each -> evidence.add(new RuleEvidence.Divides(each)));
        singled.forEach(each -> evidence.add(new RuleEvidence.Singles(each)));
        return Partitions.withEvidence(base, reading, evidence, List.of(), allowance, ruleReading,
                rulesWithoutALine, between, reaching,
                new MeasureClosure.Drawing.FromTheReading());
    }

    private ThresholdFixtures() {}
}
