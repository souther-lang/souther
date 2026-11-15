package souther.compiler.partition;

import souther.compiler.ACompiledModel;
import souther.compiler.check.AnalysisBody;
import souther.compiler.check.PredicateStatement;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.StatedContract;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.regex.PatternPlan;
import souther.compiler.values.Allowance;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What a rule of the behavior {@code f} states about the strings at a place, as the statement
 * the classes of that place are made of ({@link SetStatement}), for a test that holds the sides of
 * it to something it worked out another way.
 */
public final class SetStatementAt {

    private SetStatementAt() {
    }

    /** The one statement of what the other side of the relation can hold, about {@code place}. */
    public static SetStatement of(String source, String place) {
        return of(ACompiledModel.answered(source), place);
    }

    /** The same, of a model already compiled and answered. */
    public static SetStatement of(Compilation compilation, String place) {
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        AnalysisBody body = checked.analysisBodies().get("f");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value().get("f");
        assertNotNull(inputs, "the behavior under test is the one named");
        GuardThresholds.Guards guards = ThresholdFixtures.guardsOf("f", body,
                checked.behaviorBodies().get("f"), checked.plan(), inputs, rules);
        StatedContract stated =
                compilation.db().ask(new Bodies.StatedContracts(module)).value().get("f");
        PredicateReadings read = PredicateReadings.of("f", body, stated, inputs.reading(rules),
                inputs.parameterReads(), checked.elementBindings().get("f"),
                new RuleReachNumbering(module, "f"));
        Allowance<NumericTerm.FromOnePosition> allowance =
                Allowance.of(PatternPlan.Budget.OF_BEHAVIOR_DISTINCTIONS);
        BehaviorSetStatements.Read statements = BehaviorSetStatements.of("f", read,
                inputs.reading(rules), allowance, List.of(), new RuleReachNumbering(module, "f"),
                WhatAnAnswerTakesUp.of(inputs.reading(rules)), guards.partnered());
        List<SetStatement> at = RuleEvidence.statementsIn(statements.statements()).stream()
                .filter(each -> each.statement() instanceof PredicateStatement.CanBeTheValueOf)
                .filter(each -> each.term().toString().contains(place))
                .toList();
        assertEquals(1, at.size(), () -> "one statement about " + place + ": "
                + RuleEvidence.statementsIn(statements.statements()));
        return at.getFirst();
    }
}
