package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The walks one engine makes lend each other what the rules on their way leave.
 *
 * <p>An engine reads one body or one declaration's rules, and it reads them over and over: each
 * arm, each guard and the path to each is a walk that asks what the rules taken in so far leave.
 * Two walks that took in the same rules are asking the same question, and worked out apart it is
 * the same closure paid for twice — which, over a model whose rules relate many positions, was most
 * of what reading its invariants cost.
 */
class OneEngineWorksOutEachClosureOnceTest {

    private static final Term.Interner NAMES = new Term.Interner();

    @Test
    void twoWalksTakingInTheSameRulesWorkTheirClosureOutOnce() {
        Compilation compilation = Compilation.ofSource("module demo\n", "Main");
        RuleReadingSource rules = RuleReadings.of(compilation, compilation.modules().get(0));
        PathEngine engine = new PathEngine(
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES),
                Terms.Of.THE_DISCHARGE_TREE);
        FactSubject x = FactSubject.of(NAMES.written("x"));
        LinearForm<FactSubject> form = LinearForm.atom(x);
        Map<FactSubject, Granularity> kinds = Map.of(x, Granularity.DISCRETE);

        Known one = engine.nothingKnown().taking(form, Rel.GE, Known.Held.ON_THE_PATH, kinds);
        Known two = engine.nothingKnown().taking(form, Rel.GE, Known.Held.ON_THE_PATH, kinds);

        assertEquals(one.reachesNothing(), two.reachesNothing());
        assertEquals(1, engine.closures().workedOut(),
                "two walks of one engine worked one closure out apart");
    }
}
