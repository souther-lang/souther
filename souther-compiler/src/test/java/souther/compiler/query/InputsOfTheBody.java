package souther.compiler.query;

import souther.compiler.check.RuleReadingSource;
import souther.compiler.coverage.AlignedObservation;
import souther.compiler.inputs.InputDomain;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.ObservedValue;
import souther.compiler.partition.BehaviorInputs;
import souther.compiler.partition.Generator;
import souther.compiler.partition.ObservedInputs;

import java.util.List;

/** What a behavior of a compiled test model takes, read the way the measures read it. */
final class InputsOfTheBody {

    private InputsOfTheBody() {
    }

    /** A run that was seen going {@code seen}, answered, with no values read off it. */
    static ObservedInputs aRunSeen(AlignedObservation seen) {
        return new ObservedInputs(List.of(), new Generator.Watched.Ran(seen),
                new AnswerObservation.Answered(new ObservedValue.Bool(true)));
    }

    static BehaviorInputs of(Compilation compilation, String behavior) {
        String module = compilation.modules().get(0);
        RuleReadingSource source = Shapes.ruleReading(compilation.db(), module).value();
        InputDomain domain =
                compilation.db().ask(new Adequacy.Inputs(module)).value().get(behavior);
        return BehaviorInputs.of(Adequacy.readingOf(compilation.db(), domain, source));
    }
}
