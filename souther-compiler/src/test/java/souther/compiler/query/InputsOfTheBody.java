package souther.compiler.query;

import souther.compiler.check.RuleReadingSource;
import souther.compiler.inputs.InputDomain;
import souther.compiler.partition.BehaviorInputs;

/** What a behavior of a compiled test model takes, read the way the measures read it. */
final class InputsOfTheBody {

    private InputsOfTheBody() {
    }

    static BehaviorInputs of(Compilation compilation, String behavior) {
        String module = compilation.modules().get(0);
        RuleReadingSource source = Shapes.ruleReading(compilation.db(), module).value();
        InputDomain domain =
                compilation.db().ask(new Adequacy.Inputs(module)).value().get(behavior);
        return BehaviorInputs.of(Adequacy.readingOf(compilation.db(), domain, source));
    }
}
