package souther.compiler.partition;

import souther.compiler.ACompiledModel;
import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What a test hands a reading of one body's decision.
 *
 * <p>Read the way whoever asks the account reads it, and held to the model having compiled first: a
 * module the compile stopped in answers every question with nothing, so a measurement taken off one
 * comes back saying the body decides nothing and reads the same as a body that does.
 */
final class DecisionReadings {

    private DecisionReadings() {}

    /** {@code source} compiled once, as far as the readings of its bodies need. */
    static Compiled compiled(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        String module = compilation.modules().get(0);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        Map<String, InputDomain> inputs =
                compilation.db().ask(new Adequacy.Inputs(module)).value();
        assertNotNull(checked, "the module's bodies were checked");
        ACompiledModel.compiles(compilation);
        return new Compiled(checked, rules, inputs);
    }

    /** One module, compiled, whose bodies are read one behavior at a time. */
    record Compiled(Bodies.Elaborated checked, RuleReadingSource rules,
                    Map<String, InputDomain> inputs) {

        /** The decision {@code behavior} states. */
        DecisionReading of(String behavior) {
            AnalysisBody analysis = checked.analysisBodies().get(behavior);
            assertNotNull(analysis, "no body of `" + behavior + "` was elaborated");
            InputDomain domain = inputs.get(behavior);
            return DecisionReading.of(behavior, analysis, domain.reading(rules),
                    InputReads.ofParametersWhereCallsStand(domain.parameterReads(),
                            domain.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                            domain.dependencies()));
        }

        /** The rules of that decision, with the reading held to having been made to the end. */
        List<DecisionRule> readToTheEnd(String behavior) {
            DecisionReading read = of(behavior);
            assertEquals(new DecisionReading.Enumeration.Complete(), read.enumeration(),
                    "a body this small has its ways held apart");
            assertEquals(List.of(), read.found().stream().filter(ruled -> !ruled.whole()).toList(),
                    "and every one of them is written down whole");
            return read.rules();
        }
    }

    /** The decision {@code behavior} of {@code source} states. */
    static DecisionReading of(String source, String behavior) {
        return compiled(source).of(behavior);
    }

    /** The rules of that decision, with the reading held to having been made to the end. */
    static List<DecisionRule> readToTheEnd(String source, String behavior) {
        return compiled(source).readToTheEnd(behavior);
    }
}
