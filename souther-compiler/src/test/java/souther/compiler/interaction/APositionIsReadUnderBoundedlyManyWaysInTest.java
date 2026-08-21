package souther.compiler.interaction;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.inputs.InputDomain;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many ways in one position is read under is bounded, and by its own bound.
 *
 * <p>A second amplification and not the one on outcomes. The outcome bound is on a product taken at
 * one node — how many ways one value is settled — and this is on a product taken along the way
 * down: a condition that comes out a given way four ways over, standing inside another one, is a
 * meeting read sixteen times and a group offered sixteen times. The two multiply with the nesting
 * of the body, so one holding does not hold the other.
 *
 * <p>Over the bound an arm is read the one way a fork whose condition cannot be valued is read,
 * which is where every fork was before the ways in were told apart. So going over asks for no more
 * than was asked for then, and the reading degrades to what it used to be rather than to nothing.
 */
class APositionIsReadUnderBoundedlyManyWaysInTest {

    /**
     * A meeting under {@code depth} conditions, each of which holds two ways.
     *
     * <p>Written out rather than nested through a helper: what a helper is spliced into a body as
     * is another reading's answer, and how many ways in a position has would then be measuring that
     * as well.
     */
    private static String nestedGates(int depth) {
        List<String> names = List.of("a", "b", "c", "d", "e", "f", "g", "h", "i", "j");
        StringBuilder out = new StringBuilder("module example.gates\n\nbehavior fee : (");
        for (int gate = 0; gate < depth * 2; gate++) {
            out.append(names.get(gate)).append(": Int, ");
        }
        out.append("x: Int, y: Int) -> Int\n\nlet fee (");
        for (int gate = 0; gate < depth * 2; gate++) {
            out.append(names.get(gate)).append(", ");
        }
        out.append("x, y) =\n");
        String indent = "    ";
        for (int gate = 0; gate < depth; gate++) {
            out.append(indent).append("if ").append(names.get(gate * 2)).append(" > 1 || ")
                    .append(names.get(gate * 2 + 1)).append(" > 1 then\n");
            indent = indent + "    ";
        }
        out.append(indent).append("(if x > 1 then 1 else 0) + (if y > 1 then 10 else 0)\n");
        for (int gate = depth - 1; gate >= 0; gate--) {
            indent = indent.substring(4);
            out.append(indent).append("else 0\n");
        }
        return out.toString();
    }

    private static List<Interaction> read(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");
        Core body = checked.behaviorBodies().get(behavior);
        assertNotNull(body, "the behavior under test has a body");
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value().get(behavior);
        return Interactions.of(body, CoverageSites.of(checked.behaviorBodies()), inputs, symbols);
    }

    /** Whether any decision on any of these ways in is one that places at no class. */
    private static boolean namesAnArm(List<Interaction> found) {
        return found.stream().flatMap(group -> group.reach().stream())
                .anyMatch(decision -> decision.constrains() instanceof Condition.Arm);
    }

    /**
     * Four conditions of two ways each is sixteen ways in, and every one of them is read.
     *
     * <p>Each is a path a row can be steered down and a group nothing else asks for, so they are
     * offered — and every decision on them is a comparison, which is what places a way in at a
     * class of an input.
     */
    @Test
    void asManyWaysInAsTheBoundAllowsAreRead() {
        List<Interaction> found = read(nestedGates(4), "fee");

        assertEquals(16, found.size(), "two ways through each of four conditions: " + found);
        assertTrue(found.stream().allMatch(group -> group.factors().size() == 2),
                "and the meeting under them is the same one: " + found);
        assertEquals(false, namesAnArm(found), "each said on the comparisons: " + found);
    }

    /**
     * One condition more would be thirty-two, so that one is read the way it was read before.
     *
     * <p>Not the whole reading given up and not the ways in silently cut to the bound: the fork
     * that would go over is the one that falls back, and it falls back to naming its arm — which
     * places at no class and is what every fork was named by before any of this. What is asked for
     * over the bound is what was asked for then.
     */
    @Test
    void aConditionThatWouldGoOverTheBoundIsReadTheWayItUsedToBe() {
        List<Interaction> found = read(nestedGates(5), "fee");

        assertEquals(16, found.size(), "the ways in stop multiplying at the bound: " + found);
        assertTrue(found.stream().allMatch(group ->
                        group.reach().get(group.reach().size() - 1).constrains()
                                instanceof Condition.Arm),
                "and the condition that would have gone over names its arm: " + found);
    }
}
