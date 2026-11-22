package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
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

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The walk that says only where each construct stands ({@link ComparisonReadings#metOf}) reads
 * no condition: what an {@code if}, a {@code &&}, a {@code match} or a closure around a construct
 * states is what the arms and the applications are read under, and nothing it tells of depends on
 * it. What costs a model with costly conditions its notice is reading them, so a condition read
 * through it is a cost the notice has taken on.
 *
 * <p>The walk that does read them reads some of the same models, which is the control: without
 * it, a model of conditions the walk never reads would pass whatever the walk did.
 */
class TheWalkThatOnlySaysWhereConstructsStandReadsNoConditionTest {

    @Test
    void anIfAroundAClosureOverTheInput() {
        readsNoCondition("""
                module w1
                import List ( any )
                behavior m : (xs: List<Int>, n: Int) -> Bool
                let m (xs, n) =
                    if n > 3 then any(x -> x > n, xs) else any(x -> x + n > 9, xs)
                """);
    }

    @Test
    void anAndOfTwoConditionsAroundAClosure() {
        readsNoCondition("""
                module w1
                import List ( any )
                behavior m : (xs: List<Int>, n: Int) -> Bool
                let m (xs, n) = n > 3 && any(x -> if x > n then x > 9 else x < 2, xs)
                """);
    }

    @Test
    void aMatchOnTheInputAroundAnIf() {
        readsNoCondition("""
                module w1
                data Rule = Preceding | Following
                behavior m : (r: Rule, n: Int) -> Bool
                let m (r, n) =
                    match r with
                        | Preceding -> if n > 2 then n > 5 else n < 1
                        | Following -> n > 1
                """);
    }

    private static void readsNoCondition(String model) {
        Compilation compilation = ACompiledModel.measured(model, Adequacy.Asked.fullReport());
        String module = compilation.modules().getFirst();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value().get("m");
        AnalysisBody analysis = checked.analysisBodies().get("m");

        InputReading met = inputs.reading(rules);
        ComparisonReadings.metOf("m", analysis, met, namesOf(inputs, rules, analysis),
                ComparisonWitnesses.AtComparisons.NONE);
        assertEquals(0, WhatConditionsState.of(met).readings(),
                "the walk that only says where constructs stand read a condition");

        InputReading read = inputs.reading(rules);
        ComparisonReadings.of("m", analysis, read, namesOf(inputs, rules, analysis),
                ComparisonWitnesses.AtComparisons.NONE);
        assertTrue(WhatConditionsState.of(read).readings() > 0,
                "the walk that reads them reads some here, or this model proves nothing");
    }

    private static InputReads namesOf(InputDomain inputs, RuleReadingSource rules,
                                      AnalysisBody analysis) {
        return InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
    }
}
