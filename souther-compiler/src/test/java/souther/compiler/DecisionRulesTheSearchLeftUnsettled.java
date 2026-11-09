package souther.compiler;

import souther.compiler.partition.DecisionRule;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.DecisionEvidence;
import souther.compiler.query.RuleRequirement;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The rules of a module's decisions that no row took and the search for one settled neither way.
 *
 * <p>A rule is shown when a composed row was run and seen taking it, and excluded when the model
 * leaves it no row. What stays unsettled is a rule the search composed for and could not show, so a
 * composer that fails to hand a row a value the rule needs leaves it here.
 */
final class DecisionRulesTheSearchLeftUnsettled {

    private DecisionRulesTheSearchLeftUnsettled() {
    }

    /** Every such rule of every behavior of the module {@code module} of {@code model}. */
    static List<DecisionRule> in(String model, String module) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        List<DecisionRule> unsettled = new ArrayList<>();
        Map<String, DecisionEvidence> decisions =
                compilation.db().ask(new Adequacy.Decides(module)).value();
        for (String behavior : decisions.keySet()) {
            compilation.db().ask(new Adequacy.DecisionSearch(module, behavior)).value()
                    .forEach((rule, across) -> {
                        if (across.requirement() instanceof RuleRequirement.Unsettled) {
                            unsettled.add(rule);
                        }
                    });
        }
        return unsettled;
    }
}
