package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A comparison is accounted for where it is written, and not where a fork was found.
 *
 * <p>The other half of moving what bears a line off the fork. What a body states at a position is
 * said by the comparison and read by whoever finds one, so a reading that started from an
 * {@code if} left a comparison written anywhere else neither a line nor a rule it could not read —
 * it left it unmentioned, which is the one answer that says the model states nothing there.
 *
 * <p>Written as a body with no fork in it at all. Under a fork the old reading and this one agree,
 * so a model with one in it cannot tell them apart.
 */
class AComparisonIsAccountedForWhereverItIsWrittenTest {

    private static GuardThresholds.Guards read(String body) {
        String source = """
                module example.written

                data Pair = { x: Int, y: Int }

                behavior pick : (p: Pair) -> Bool
                let pick (p) = BODY
                """.replace("BODY", body);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, () -> "the model under test compiles: " + body);
        Core core = checked.behaviorBodies().get("pick");
        assertNotNull(core);
        CoverageSites.Plan plan = checked.plan();
        return GuardThresholds.of(core, plan,
                compilation.db().ask(new Adequacy.Inputs(module)).value().get("pick"), symbols);
    }

    /**
     * A comparison a behavior answers with, in a shape this cannot read, is still said to be a rule
     * written at the position.
     *
     * <p>{@code Int.multiply(p.x, p.x)} names the position and is not a number a line can be drawn
     * on, so this is the answer that separates "the model draws a line here this could not read"
     * from "the model draws none". Written under a fork, the reading already gave it; written as the
     * answer, it gave nothing.
     */
    @Test
    void aComparisonAnsweredWithIsNoticedEvenWhereNoLineCameOfIt() {
        GuardThresholds.Guards guards = read("Int.multiply(p.x, p.x) < 10");

        assertEquals(List.of(), guards.thresholds());
        assertEquals(1, guards.rulesWithoutALine().size(), guards.rulesWithoutALine().toString());
    }
}
