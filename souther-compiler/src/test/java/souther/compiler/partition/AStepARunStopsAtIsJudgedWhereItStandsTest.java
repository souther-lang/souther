package souther.compiler.partition;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import souther.compiler.ACompiledModel;
import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A quotient whose divisor may be nought is shown to stop a run where it stands, at the value of
 * the input that takes the divisor there: whether a comparison is written in it, after it over
 * the name its value is given, after it over something else, or nowhere, and whether a condition
 * that comes after it would keep the divisor from nought. A run that stops there has got to none
 * of what comes after.
 */
class AStepARunStopsAtIsJudgedWhereItStandsTest {

    private static final String MODEL = """
            module demo

            data In = { p: Int, q: Int }

            behavior inTheComparison : (i: In) -> Int
            let inTheComparison (i) = if Rational.toInt(DOWN, 4 / i.p) >= 2 then 1 else 2

            behavior givenToANameTheComparisonReads : (i: In) -> Int
            let givenToANameTheComparisonReads (i) = {
                let r = Rational.toInt(DOWN, 4 / i.p)
                if r >= 2 then 1 else 2 }

            behavior withNoComparison : (i: In) -> Int
            let withNoComparison (i) = Rational.toInt(DOWN, 4 / i.p)

            behavior beforeAConditionThatKeepsItFromNought : (i: In) -> Int
            let beforeAConditionThatKeepsItFromNought (i) = {
                let r = Rational.toInt(DOWN, 4 / i.p)
                if i.p /= 0 then (if r >= 2 then 1 else 2) else 3 }

            behavior givenToANameNothingReads : (i: In) -> Int
            let givenToANameNothingReads (i) = {
                let r = Rational.toInt(DOWN, 4 / i.p)
                if i.q >= 2 then 1 else 2 }
            """;

    @ParameterizedTest
    @ValueSource(strings = {"inTheComparison", "givenToANameTheComparisonReads",
            "withNoComparison", "beforeAConditionThatKeepsItFromNought",
            "givenToANameNothingReads"})
    void theQuotientIsShownToStopARunAtTheDivisorAtNought(String behavior) {
        StopsOfABody.AtAStep quotient = judged(behavior).stream()
                .filter(each -> each.step() instanceof Core.Binary)
                .findFirst().orElseThrow();
        assertEquals(1, quotient.operations().size(), quotient.toString());
        assertTrue(quotient.operations().getFirst()
                        instanceof StopAssessment.Judgement.Stops(StopAssessment.Shown shown)
                        && shown.site() instanceof StopAssessment.Site.ByNought
                        && ExactRatio.ZERO.equals(shown.at().get(
                                new NumericTerm.ValueOf(TermPath.of("i").then("p")))),
                quotient.toString());
    }

    /** The model, compiled once for every behavior asked of it. */
    private static final Compilation COMPILED = ACompiledModel.measured(MODEL,
            new Adequacy.Asked(Adequacy.Level.OFF, false));

    private static List<StopsOfABody.AtAStep> judged(String behavior) {
        Compilation compilation = COMPILED;
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
}
