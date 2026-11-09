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
        return settledAs(RuleRequirement.Unsettled.class, model, module);
    }

    /**
     * Every rule the search excluded: shown to have no row at all. A rule a row was composed for
     * and a run took is {@link RuleRequirement.Required}, and neither of these; so a model whose
     * every rule is taken by some row has none here and none in {@link #in}.
     */
    static List<DecisionRule> excludedIn(String model, String module) {
        return settledAs(RuleRequirement.Excluded.class, model, module);
    }

    /** The rules of the model that no run took: those left unsettled and those excluded. For a
     *  model whose every rule some row takes, none. */
    static List<DecisionRule> notShownIn(String model, String module) {
        List<DecisionRule> out = new ArrayList<>(in(model, module));
        out.addAll(excludedIn(model, module));
        return out;
    }

    private static List<DecisionRule> settledAs(Class<? extends RuleRequirement> kind,
                                                String model, String module) {
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
                        if (kind.isInstance(across.requirement())) {
                            unsettled.add(rule);
                        }
                    });
        }
        return unsettled;
    }
}
