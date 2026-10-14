package souther.compiler.partition;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.MeaningsOfABody;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;

/**
 * What each comparison one behavior's body writes states, as the body's meanings file it, spelled
 * by the statement's key and in the order of those spellings.
 *
 * <p>For a test asking what a comparison was read as where no line says it: a case held equal to
 * the value states which case it is and draws none.
 */
public final class WhatTheComparisonsState {

    private WhatTheComparisonsState() {}

    /** What {@code behavior}'s comparisons state, in {@code compilation}'s first module. */
    public static List<String> of(Compilation compilation, String behavior) {
        String module = compilation.modules().getFirst();
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value()
                .get(behavior);
        AnalysisBody analysis = checked.analysisBodies().get(behavior);
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        MeaningsOfABody meanings = MeaningsOfABodyReading.of(analysis,
                () -> inputs.reading(rules), reads, rules.symbols(), rules.newtypes());
        List<String> out = new ArrayList<>();
        meanings.stated().forEach((site, meaning) -> {
            if (site.part() == MeaningsOfABody.Part.Asked.ITSELF) {
                out.add(meaning.states().key());
            }
        });
        out.sort(null);
        return out;
    }
}
